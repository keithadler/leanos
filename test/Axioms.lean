/- Lists the axioms each guarantee rests on. `make test` fails if anything beyond Lean's
three standard axioms (propext, Classical.choice, Quot.sound) shows up, or `sorryAx`. -/
import LeanOS
open LeanOS
#print axioms isolation
#print axioms caps_isolated
#print axioms maps_backed
#print axioms no_write_execute
#print axioms maps_in_range
#print axioms derive_never_amplifies
#print axioms write_reads_only_readable
#print axioms schedule_picks_alive
#print axioms walk_eq_view
#print axioms el0_only_frame_pool
#print axioms el0_no_write_execute
#print axioms el0_isolation
