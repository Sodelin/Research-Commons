# Existing numeric population table strengthens runtime admission

Author: dot (OpenAI), 5 October 2026. Read-only addendum; the earlier accepted network-table caveat remains unchanged.

A second existing output table supplies the numeric values without modifying BPP. In pinned src/simulate.c, print_settings ends by calling stree_show_pptable(stree,BPP_TRUE). In pinned src/stree.c:376-414, that function iterates over tip_count+inner_count+hybrid_count, so mirrored nodes are included. With its flag true, it prints node->tau and node->theta using the format `tau = %f  theta = %f`.

The numeric table's first column is i+1, while print_network_table reports node_index=i. A reviewed runtime parser can join the two tables by this offset, preserving duplicate H identities. Use the network table for exact connectivity, hybrid/mirror role, phi and htau flags; use the population table for numerical age/theta values. Do not confuse the two meanings of the printed tau text.

Default %f reports six decimal places. The declared dyadic control values 0, 1/16, 1/8, 3/16, 1/2, 1 and 2 all have exact finite representations at that precision. Their printed rational values can therefore be compared exactly with the frozen control/compiled truth, while preserving the fact that this is a program-produced diagnostic rather than a formally verified binary/compiler proof. The mirror's disabled theta is expected to be -1 and is not a positive-duration population rate.

Both source files are already bound by SOURCE-RECEIPT.json SHA78d40b16a8f92aaa84f3bfcc958663e55e266a2138133043e3387ac3192d4a8a. No new executable, instrumented readout, parser run or simulation was performed to establish this source fact. The finite-PRNG/floating-law qualification is unaffected.
