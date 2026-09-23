/- Lists the axioms each guarantee rests on. `make test` fails if anything beyond Lean's
three standard axioms (propext, Classical.choice, Quot.sound) shows up, or `sorryAx`. -/
import LeanOS
open LeanOS
#print axioms frame_flow
#print axioms endpoints_fixed
#print axioms maps_backed
#print axioms no_write_execute
#print axioms maps_in_range
#print axioms mapping_flow
#print axioms derive_never_amplifies
#print axioms edge_iff
#print axioms mallory_confined
#print axioms carol_confined
#print axioms alice_confined
#print axioms server_frames
#print axioms write_reads_only_readable
#print axioms schedule_picks_ready
#print axioms walk_eq_view
#print axioms el0_only_pool_or_fb
#print axioms physOf_inj
#print axioms el0_no_write_execute
#print axioms el0_flow
#print axioms el0_shared
#print axioms el0_mallory_isolated
