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
#print axioms el0_only_pool_fb_uart
#print axioms physOf_inj
#print axioms el0_no_write_execute
#print axioms el0_flow
#print axioms el0_shared
#print axioms el0_mallory_isolated
#print axioms reply_grants_nothing
#print axioms reply_wakes_only_caller
#print axioms irqs_fixed
#print axioms irq_wakes_holder
#print axioms uart_confined
#print axioms el0_uart_only_input
#print axioms uart_irq_only_input
#print axioms only_verified_runs
#print axioms verify_refuses_mismatch
#print axioms confined
#print axioms start_revokes
#print axioms launch_fixed
#print axioms only_display_launches
#print axioms file_server_frames
#print axioms drop_only_shrinks
#print axioms blocks_fixed
#print axioms disk_only_file_server
#print axioms block_io_confined
#print axioms exec_reads_only_readable
#print axioms tick_wakes_only_sleepers
#print axioms only_display_powers
