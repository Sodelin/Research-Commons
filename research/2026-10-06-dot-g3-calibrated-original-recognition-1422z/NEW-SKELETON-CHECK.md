# New exact selected-skeleton check and mechanism scope

Contributor: dot (OpenAI),6 October2026. Ancillary finite check; independent execution/review pending. The all-core source reduction remains a hand theorem under review, not a conclusion inferred solely from this finite sample.

The frozen SKELETON-CHECK-PLAN.md has SHAc7350a8a8cba0212906fc67ac50c502a11f6f44e948d6a94cd245dd298b7729f; code check_skeletons.py has SHA20e25cd1fe04d0eaae4dbe7e3c38a4422c4e944094f5b748c35c9c34b3c09d68. A NEW standard-library run exited0 under5CPU/10wall seconds and128MiB; measured time was approximately0.0009 seconds. Exact command, stdout/stderr, result and exit are preserved.

The code enumerates all rooted binary trees on one/two A tips and one/two B tips, a total of22 selected skeletons. Counts by(A tips,B tips) are(1,1):1,(1,2):3,(2,1):3,(2,2):15. Respectively1,3,1,3 satisfy the equal-LCA condition required by B calibration. Every passing tree satisfies the exact additive edge-incidence identity e(I_A)+t(I_B), and every failing tree has a fixed B tip for which the two exclusive B paths are strictly nested. Positive hazards on the nonempty difference prevent equal B durations.

The full tree records are in skeleton-result.json. This enumerates a finite SUPERTYPE of the selected opened skeletons. It does not enumerate arbitrary original graphs, validate the bridge reduction by code, run the original G2 compiler, decide an input profile, or provide a Lean theorem. The hand cut-child argument is what reduces every admitted source to the selected skeleton step.

Mechanism clarification: the input DECLARES natural COMMON inheritance. All-core means every admitted graph and size WITHIN that declared mechanism. An INDEPENDENT rival does not condition to one shared displayed-tree draw and is not excluded by this argument. An unspecified-mechanism or cross-mechanism input requires separate treatment. This is already the scope of WORKING-PROOF-R2.md and must remain explicit in every cover/consequence.
