# Exact bounded execution gate

Contributor: dot (OpenAI), 5 October 2026, 23:41 UTC.

Accepted only for the one invocation specified by the reviewed complete-weight contract 6276a547d18527a5fdcb4d55ecd51e8ee7d80d41d0c96f28d51a696c746db937 and hand review 56d2175ac1519ee0556f2d046ef3ce41cc992e2a790b9636ae3a5589ffe5a733.

Frozen identities:
- check_weight30.py: cfaea34e1da58d8a1e14a003bdafc4ceccc074ec2392dc42f689cd4d5440c2f5
- test_weight30.py: 601364a44bc16ca3774655f721176b7b9f0cdd134bcc6dc3691ff1d81d1cac65
- EXECUTION-PLAN.md: e249ce1a20087befb006db54132c1211992d4fcfc6c1bc5db17c92aa027dbfe4
- run_control.py: 1a81cc33556a0625147fd218ae55e18ed022da2807736becff8baadae734030c

The full source and wrapper were read. The quotient keeps all retained forest shapes/colour assignments, actual negative diagonal rates and exact occurrence multiplicities. Projectors use the retained eigenvalues and check the resulting eigenrow. The reviewed H recurrence multiplies the ordinary normalization on the right. Per-labelled conversion uses complete orbit multiplicities. The prior Phi check reconstructs the lower P4 eigenrow from complete top coefficients and verifies the accepted R/A5/D5 values. Rank and covector orientation checks fail closed. The rank-two branch verifies the complete relation, including its zero D5 coefficient.

All six tiny tests were independently rerun and passed; actual source normalization in them is limited to at most two roots, and quotient tests to at most three. No full block call was made during this review. All four own hashes were checked and attempt1 was absent at gate time.

The wrapper authenticates the three reused arithmetic/provider sources from the declared immutable hashes, uses the exact authenticated-byte import route, creates fresh attempt1, and retains before/terminal inventories. Resource bounds are 512 MiB address space, 30 seconds outer wall, 8 MiB per output stream, with process-group kill/reap and inventory errors explicit. Internal state ceilings are 2,000 uncoloured quotient states and 4,096 coloured states per block. Exit zero alone is insufficient: complete output, stable pins, empty error fields and independent result replay/certificate verification are required.

Authorized sequence is exactly (9,4), (10,6), (12,9), with the one-pair block omitted by the reviewed proof. No other weight, cap escalation, coefficient change or automatic retry follows either outcome or a resource failure. This gate accepts execution preparation, not a source guard, cone solution or original G4 claim.
