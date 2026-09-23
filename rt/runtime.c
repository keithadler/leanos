/*
 * The part of Lean's runtime that compiled Lean code needs, written for bare metal.
 *
 * Lean's own runtime is C++ with threads, GMP and an OS allocator. The kernel needs far
 * less: allocation, reference counting, closures, and a few arrays. Everything outside
 * that stops the machine with a message, so any code path that reaches for more of the
 * runtime fails loudly and never silently gives a wrong answer.
 *
 * Limits, all enforced by stopping the machine:
 *   - Numbers are small only: a Nat of 2^63 or more stops the kernel (see lean_nat_big_*).
 *   - Single core, single threaded: objects never become multi-threaded.
 *   - No strings, thunks, tasks, or external objects.
 * This file is trusted, not proved. TRUST.md lists it.
 */
#include <lean/lean.h>
#include "../arch/arch.h"

/* ---------- allocator ----------
 * Size classes: 16-byte steps up to 4 KiB, then powers of two. Each block carries its class
 * in an 8-byte header so free() needs no size. Freed blocks go to a per-class free list;
 * fresh memory comes from a bump pointer over the heap between the kernel image and the
 * user frames. Nothing is ever returned to the bump pointer. */

extern char __heap_start[];
#define HEAP_END ((char *)FRAME_BASE)
#define SMALL_CLASSES 258 /* 16 .. 4112 bytes */
#define NCLASSES (SMALL_CLASSES + 24)

static char *heap_top;
static void *free_lists[NCLASSES];
static uint64_t heap_live, heap_peak;

static unsigned size_class(size_t n, size_t *rounded) {
    if (n <= 16 * (SMALL_CLASSES - 1)) {
        unsigned c = (unsigned)((n + 15) / 16);
        *rounded = (size_t)c * 16;
        return c;
    }
    size_t sz = 8192;
    unsigned c = SMALL_CLASSES;
    while (sz < n) { sz <<= 1; c++; }
    if (c >= NCLASSES) kpanic("allocation too large");
    *rounded = sz;
    return c;
}

void *malloc(size_t n) {
    if (!heap_top) heap_top = (char *)(((uintptr_t)__heap_start + 15) & ~(uintptr_t)15);
    size_t rounded;
    unsigned c = size_class(n, &rounded);
    uint64_t *blk = free_lists[c];
    if (blk) {
        free_lists[c] = *(void **)(blk + 2);
    } else {
        if (heap_top + 16 + rounded > HEAP_END) kpanic("kernel heap exhausted");
        blk = (uint64_t *)heap_top;
        heap_top += 16 + rounded;
    }
    blk[0] = c;
    heap_live += rounded;
    if (heap_live > heap_peak) heap_peak = heap_live;
    return blk + 2; /* 16 bytes of header keep payloads 16-byte aligned */
}

void free(void *p) {
    if (!p) return;
    uint64_t *blk = (uint64_t *)p - 2;
    unsigned c = (unsigned)blk[0];
    if (c >= NCLASSES) kpanic("free of a block this allocator did not hand out");
    size_t rounded;
    if (c < SMALL_CLASSES) rounded = (size_t)c * 16;
    else rounded = (size_t)8192 << (c - SMALL_CLASSES);
    heap_live -= rounded;
    *(void **)(blk + 2) = free_lists[c];
    free_lists[c] = blk;
}

void free_sized(void *p, size_t n) { (void)n; free(p); }

uint64_t rt_heap_live(void) { return heap_live; }
uint64_t rt_heap_peak(void) { return heap_peak; }

/* Big objects (arrays) use the same header layout lean.h uses for small ones. */
lean_object *lean_alloc_object(size_t sz) {
    size_t *mem = malloc(sizeof(size_t) + sz);
    *mem = sz;
    return (lean_object *)(mem + 1);
}

void lean_free_object(lean_object *o) { free((size_t *)o - 1); }

size_t lean_object_byte_size(lean_object *o) { return *((size_t *)o - 1); }

void lean_inc_heartbeat(void) {}

/* ---------- reference counting ----------
 * Called when a count drops to zero. Children whose counts also reach zero go on an
 * explicit stack, so freeing a long list never recurses deeply. */

#define FREE_STACK 4096
static lean_object *free_stack[FREE_STACK];

static void push_dead(lean_object *o, unsigned *top) {
    if (lean_is_scalar(o)) return;
    int rc = lean_internal_get_rc(o);
    if (rc == 0) return;                 /* persistent: never freed */
    if (rc > 1) { lean_internal_sub_rc(o, 1); return; }
    if (rc < 0) kpanic("multi-threaded object in a single-threaded kernel");
    if (*top == FREE_STACK) kpanic("free stack overflow");
    free_stack[(*top)++] = o;
}

void lean_dec_ref_cold(lean_object *o) {
    if (lean_internal_get_rc(o) != 1) {
        if (lean_internal_get_rc(o) > 1) lean_internal_sub_rc(o, 1);
        return;
    }
    unsigned top = 0;
    free_stack[top++] = o;
    while (top) {
        lean_object *x = free_stack[--top];
        uint8_t tag = lean_ptr_tag(x);
        if (tag <= LeanMaxCtorTag) {
            unsigned n = lean_ctor_num_objs(x);
            for (unsigned i = 0; i < n; i++) push_dead(lean_ctor_get(x, i), &top);
            lean_free_small_object(x);
        } else if (tag == LeanClosure) {
            unsigned n = lean_closure_num_fixed(x);
            for (unsigned i = 0; i < n; i++) push_dead(lean_closure_get(x, i), &top);
            lean_free_small_object(x);
        } else if (tag == LeanArray) {
            size_t n = lean_array_size(x);
            for (size_t i = 0; i < n; i++) push_dead(lean_array_get_core(x, i), &top);
            lean_free_object(x);
        } else if (tag == LeanScalarArray || tag == LeanString) {
            lean_free_object(x);
        } else {
            kpanic("freeing an object kind the kernel runtime does not support");
        }
    }
}

void lean_inc_ref_huge_n(lean_object *o, size_t n) {
    (void)o; (void)n;
    kpanic("reference count increment too large");
}

void lean_mark_persistent(lean_object *o) {
    if (!lean_is_scalar(o)) o->m_rc = 0;
}

void lean_mark_mt(lean_object *o) { (void)o; }

/* ---------- one-time initialization of closed terms ---------- */

lean_object *lean_obj_once_cold(lean_object **loc, lean_once_cell_t *tok, lean_object *(*init)(void)) {
    if (tok->state != 1) {
        lean_object *v = init();
        lean_mark_persistent(v);
        *loc = v;
        tok->state = 1;
    }
    return *loc;
}

#define ONCE(name, T)                                                              \
    T name(T *loc, lean_once_cell_t *tok, T (*init)(void)) {                       \
        if (tok->state != 1) { *loc = init(); tok->state = 1; }                    \
        return *loc;                                                               \
    }
ONCE(lean_uint8_once_cold, uint8_t)
ONCE(lean_uint16_once_cold, uint16_t)
ONCE(lean_uint32_once_cold, uint32_t)
ONCE(lean_uint64_once_cold, uint64_t)
ONCE(lean_usize_once_cold, size_t)

/* ---------- closures ---------- */

typedef lean_object *O;

static O call_fun(void *f, unsigned n, O *a) {
    switch (n) {
    case 1: return ((O(*)(O))f)(a[0]);
    case 2: return ((O(*)(O, O))f)(a[0], a[1]);
    case 3: return ((O(*)(O, O, O))f)(a[0], a[1], a[2]);
    case 4: return ((O(*)(O, O, O, O))f)(a[0], a[1], a[2], a[3]);
    case 5: return ((O(*)(O, O, O, O, O))f)(a[0], a[1], a[2], a[3], a[4]);
    case 6: return ((O(*)(O, O, O, O, O, O))f)(a[0], a[1], a[2], a[3], a[4], a[5]);
    case 7: return ((O(*)(O, O, O, O, O, O, O))f)(a[0], a[1], a[2], a[3], a[4], a[5], a[6]);
    case 8: return ((O(*)(O, O, O, O, O, O, O, O))f)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]);
    case 9: return ((O(*)(O, O, O, O, O, O, O, O, O))f)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8]);
    case 10: return ((O(*)(O, O, O, O, O, O, O, O, O, O))f)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9]);
    case 11: return ((O(*)(O, O, O, O, O, O, O, O, O, O, O))f)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10]);
    case 12: return ((O(*)(O, O, O, O, O, O, O, O, O, O, O, O))f)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11]);
    case 13: return ((O(*)(O, O, O, O, O, O, O, O, O, O, O, O, O))f)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12]);
    case 14: return ((O(*)(O, O, O, O, O, O, O, O, O, O, O, O, O, O))f)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13]);
    case 15: return ((O(*)(O, O, O, O, O, O, O, O, O, O, O, O, O, O, O))f)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13], a[14]);
    case 16: return ((O(*)(O, O, O, O, O, O, O, O, O, O, O, O, O, O, O, O))f)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13], a[14], a[15]);
    default: return ((O(*)(O *))f)(a); /* arity above LEAN_CLOSURE_MAX_ARGS takes an array */
    }
}

/* Move (if f is unshared) or copy (if shared) f's fixed arguments into out, consuming f. */
static void take_fixed(O f, O *out) {
    unsigned k = lean_closure_num_fixed(f);
    if (lean_is_exclusive(f)) {
        for (unsigned i = 0; i < k; i++) out[i] = lean_closure_get(f, i);
        lean_free_small_object(f);
    } else {
        for (unsigned i = 0; i < k; i++) { out[i] = lean_closure_get(f, i); lean_inc(out[i]); }
        lean_dec(f);
    }
}

lean_object *lean_apply_n(lean_object *f, unsigned n, lean_object **args) {
    while (n > 0) {
        if (lean_is_scalar(f) || !lean_is_closure(f)) kpanic("apply of a non-function");
        unsigned arity = lean_closure_arity(f);
        unsigned k = lean_closure_num_fixed(f);
        if (arity > 64) kpanic("closure arity too large");
        if (k + n < arity) {
            O g = lean_alloc_closure(lean_closure_fun(f), arity, k + n);
            O buf[64];
            take_fixed(f, buf);
            for (unsigned i = 0; i < k; i++) lean_closure_set(g, i, buf[i]);
            for (unsigned i = 0; i < n; i++) lean_closure_set(g, k + i, args[i]);
            return g;
        }
        unsigned used = arity - k;
        O all[64];
        void *fun = lean_closure_fun(f);
        take_fixed(f, all);
        for (unsigned i = 0; i < used; i++) all[k + i] = args[i];
        f = call_fun(fun, arity, all);
        args += used;
        n -= used;
    }
    return f;
}

lean_object *lean_apply_m(lean_object *f, unsigned n, lean_object **args) { return lean_apply_n(f, n, args); }

#define APPLY(k, ...)                                            \
    lean_object *lean_apply_##k(lean_object *f, __VA_ARGS__) {   \
        O a[] = {APPLY_ARGS_##k};                                \
        return lean_apply_n(f, k, a);                            \
    }
#define APPLY_ARGS_1 a1
#define APPLY_ARGS_2 a1, a2
#define APPLY_ARGS_3 a1, a2, a3
#define APPLY_ARGS_4 a1, a2, a3, a4
#define APPLY_ARGS_5 a1, a2, a3, a4, a5
#define APPLY_ARGS_6 a1, a2, a3, a4, a5, a6
APPLY(1, O a1)
APPLY(2, O a1, O a2)
APPLY(3, O a1, O a2, O a3)
APPLY(4, O a1, O a2, O a3, O a4)
APPLY(5, O a1, O a2, O a3, O a4, O a5)
APPLY(6, O a1, O a2, O a3, O a4, O a5, O a6)

/* ---------- arrays ---------- */

lean_object *lean_copy_expand_array(lean_object *a, bool expand) {
    size_t sz = lean_array_size(a), cap = lean_array_capacity(a);
    if (expand) cap = cap ? 2 * cap : 4;
    if (cap < sz) cap = sz;
    O r = lean_alloc_array(sz, cap);
    O *src = lean_array_cptr(a), *dst = lean_array_cptr(r);
    if (lean_is_exclusive(a)) {
        for (size_t i = 0; i < sz; i++) dst[i] = src[i];
        lean_free_object(a);
    } else {
        for (size_t i = 0; i < sz; i++) { dst[i] = src[i]; lean_inc(dst[i]); }
        lean_dec(a);
    }
    return r;
}

lean_object *lean_array_push(lean_object *a, lean_object *v) {
    if (!lean_is_exclusive(a) || lean_array_size(a) == lean_array_capacity(a))
        a = lean_copy_expand_array(a, lean_array_size(a) == lean_array_capacity(a));
    lean_array_object *o = lean_to_array(a);
    o->m_data[o->m_size++] = v;
    return a;
}

lean_object *lean_mk_array(lean_object *n, lean_object *v) {
    if (!lean_is_scalar(n)) kpanic("array too large");
    size_t sz = lean_unbox(n);
    O r = lean_alloc_array(sz, sz);
    for (size_t i = 0; i < sz; i++) lean_array_cptr(r)[i] = v;
    if (sz == 0) lean_dec(v);
    else if (sz > 1) lean_inc_n(v, sz - 1);
    return r;
}

lean_object *lean_array_mk(lean_object *l) {
    O r = lean_alloc_array(0, 4);
    O it = l;
    while (!lean_is_scalar(it)) {
        O h = lean_ctor_get(it, 0);
        lean_inc(h);
        r = lean_array_push(r, h);
        it = lean_ctor_get(it, 1);
    }
    lean_dec(l);
    return r;
}

lean_object *lean_array_to_list(lean_object *a) {
    O l = lean_box(0);
    size_t n = lean_array_size(a);
    for (size_t i = n; i > 0; i--) {
        O h = lean_array_get_core(a, i - 1);
        lean_inc(h);
        O c = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(c, 0, h);
        lean_ctor_set(c, 1, l);
        l = c;
    }
    lean_dec(a);
    return l;
}

lean_object *lean_array_get_panic(lean_object *def) {
    kputs("lean: array index out of bounds\n");
    return def;
}

lean_object *lean_array_set_panic(lean_object *a, lean_object *v) {
    kputs("lean: array index out of bounds\n");
    lean_dec(v);
    return a;
}

/* ---------- numbers ---------- */

#define TOO_BIG(name, ...) \
    lean_object *name(__VA_ARGS__) { kpanic("number too large for the kernel runtime (" #name ")"); }
TOO_BIG(lean_nat_big_succ, O a)
TOO_BIG(lean_nat_big_add, O a, O b)
TOO_BIG(lean_nat_big_sub, O a, O b)
TOO_BIG(lean_nat_big_mul, O a, O b)
TOO_BIG(lean_nat_overflow_mul, size_t a, size_t b)
TOO_BIG(lean_nat_big_div, O a, O b)
TOO_BIG(lean_nat_big_mod, O a, O b)
TOO_BIG(lean_nat_big_land, O a, O b)
TOO_BIG(lean_nat_big_lor, O a, O b)
TOO_BIG(lean_nat_big_xor, O a, O b)
TOO_BIG(lean_nat_big_shiftr, O a, O b)
TOO_BIG(lean_big_usize_to_nat, size_t n)
TOO_BIG(lean_big_uint64_to_nat, uint64_t n)
bool lean_nat_big_eq(O a, O b) { kpanic("number too large for the kernel runtime (eq)"); }
bool lean_nat_big_le(O a, O b) { kpanic("number too large for the kernel runtime (le)"); }
bool lean_nat_big_lt(O a, O b) { kpanic("number too large for the kernel runtime (lt)"); }

/* Numbers of 2^63 and above appear in the standard library's closed terms (`UInt64.size`
   and `USize.size`, built from a literal or from `2 ^ 64`) that module initialization
   computes even though the kernel never uses them. Such a number becomes an opaque
   persistent object tagged as a big number: any arithmetic or comparison on it goes to a
   lean_nat_big_* function above and stops the machine. */
static lean_object *big_placeholder(void) {
    lean_object *big = lean_alloc_small_object(sizeof(lean_object) + 8);
    lean_set_st_header(big, LeanMPZ, 0);
    big->m_rc = 0;
    return big;
}

lean_object *lean_nat_shiftl(O a, O b) {
    if (lean_is_scalar(a) && lean_is_scalar(b)) {
        size_t x = lean_unbox(a), s = lean_unbox(b);
        if (x == 0) return lean_box(0);
        if (s < 62 && (x >> (62 - s)) == 0) return lean_box(x << s);
        return big_placeholder();
    }
    kpanic("number too large for the kernel runtime (shiftl)");
}

lean_object *lean_nat_pow(O a, O b) {
    if (!lean_is_scalar(a) || !lean_is_scalar(b)) kpanic("number too large (pow)");
    size_t x = lean_unbox(a), e = lean_unbox(b), r = 1;
    while (e--) {
        if (__builtin_mul_overflow(r, x, &r) || r > LEAN_MAX_SMALL_NAT) return big_placeholder();
    }
    return lean_box(r);
}

lean_object *lean_cstr_to_nat(char const *s) {
    size_t r = 0;
    for (; *s; s++) {
        if (__builtin_mul_overflow(r, 10, &r) || __builtin_add_overflow(r, (size_t)(*s - '0'), &r) ||
            r > LEAN_MAX_SMALL_NAT)
            return big_placeholder();
    }
    return lean_box(r);
}

#define BIG_TO(name, T) T name(O a) { kpanic("number too large for the kernel runtime (" #name ")"); }
BIG_TO(lean_uint8_of_big_nat, uint8_t)
BIG_TO(lean_uint16_of_big_nat, uint16_t)
BIG_TO(lean_uint32_of_big_nat, uint32_t)
BIG_TO(lean_uint64_of_big_nat, uint64_t)
BIG_TO(lean_usize_of_big_nat, size_t)

lean_object *lean_system_platform_nbits(lean_object *unit) { (void)unit; return lean_box(64); }

/* ---------- panics and unsupported features ---------- */

lean_object *lean_panic_fn(lean_object *def, lean_object *msg) {
    kputs("lean panic: ");
    if (!lean_is_scalar(msg) && lean_ptr_tag(msg) == LeanString) kputs(lean_string_cstr(msg));
    kpanic("");
    (void)def;
}

lean_object *lean_panic_fn_borrowed(lean_object *def, lean_object *msg) { return lean_panic_fn(def, msg); }

void lean_internal_panic(char const *msg) { kpanic(msg); }
void lean_internal_panic_out_of_memory(void) { kpanic("out of memory"); }
void lean_internal_panic_unreachable(void) { kpanic("unreachable code reached"); }
void lean_internal_panic_rc_overflow(void) { kpanic("reference count overflow"); }
void lean_internal_panic_overflow(void) { kpanic("integer overflow"); }

lean_object *lean_sorry(uint8_t u) { (void)u; kpanic("executed `sorry`"); }

#define UNSUPPORTED(name, R, ...) \
    R name(__VA_ARGS__) { kpanic(#name " is not supported by the kernel runtime"); }
UNSUPPORTED(lean_byte_array_data, O, O a)
UNSUPPORTED(lean_byte_array_mk, O, O a)
UNSUPPORTED(lean_byte_array_push, O, O a, uint8_t b)
UNSUPPORTED(lean_name_eq, uint8_t, O a, O b)
UNSUPPORTED(lean_string_eq_cold, bool, O a, O b)
UNSUPPORTED(lean_string_from_utf8_unchecked, O, O a)
UNSUPPORTED(lean_string_hash, uint64_t, O a)
UNSUPPORTED(lean_string_mk, O, O a)
UNSUPPORTED(lean_string_to_utf8, O, O a)
UNSUPPORTED(lean_mk_string_unchecked, O, char const *s, size_t sz, size_t len)
UNSUPPORTED(lean_mk_string, O, char const *s)
UNSUPPORTED(lean_string_push, O, O s, uint32_t c)
UNSUPPORTED(lean_string_append, O, O a, O b)
