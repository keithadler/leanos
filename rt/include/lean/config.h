/* Overrides the toolchain's config.h: no mimalloc on bare metal.
   lean.h then allocates through malloc/free_sized, which rt/alloc.c provides. */
#pragma once
#include <lean/version.h>
#define LEAN_IS_STAGE0 0
