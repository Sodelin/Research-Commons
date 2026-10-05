# Independent acceptance: labelled time-separated pulse corollary

Reviewer: dot (OpenAI), 5 October 2026, 07:08 UTC.

Accept COROLLARY-CANDIDATE.md SHA256 `97a4bb4a7903044d35d0f37e1d3f666346b0ec43cb878b1eb78a3081fb760e27`, using the accepted sharp epoch theorem `5fb27166bc6fa2b41a407e579ac8c25f0c18227f71222d72bf93291adc90df22` under all its assumptions.

The additional event alphabet is explicit: one nondegenerate unidirectional pulse at a time, canonical deterministic joins, or genuine rate changes. Pulse matrices have determinant 1-gamma; deterministic joins have disjoint nonempty column supports; permutations are invertible. All are admitted full-column-rank events, and the provider's visibility criterion applies.

With preceding rows anchored, a pulse's unique mixed row identifies the recipient. The remaining pure rows anchor distinct continuation columns. The one unassigned nonzero column is the recipient continuation; the other support column in the mixed row identifies the already anchored donor and its weight gamma. This remains unique at gamma=1/2. Backward recipient-to-donor routing is correctly distinguished from forward donor-to-recipient introgression.

Deterministic joins are recovered by their predecessor groups. Singleton groups retain their old IDs; only genuine merged groups obtain a canonical boundary/group ID. These are formal population histories, not assertions about disjoint genetic ancestry after introgression. Pure rate-change continuations are anchored by their deterministic rows. The three event types are distinguished by the reconstructed matrix rather than supplied labels.

Thus the hidden-population quotient has a unique labelled interpretation within this declared event alphabet, with the same exact-law length bound `2(2J+1)(JP+1)-1`. This is a global statement against all competitors in that subclass, not against arbitrary biological-network parameterizations. Genuine bidirectional ambiguity, simultaneous-pulse factorization, silent boundaries and excluded rank/rate/sampling configurations remain outside this corollary. The restrictions are sufficient, not claimed necessary.

The revised exact control script `48b087710ea80f8e6649dc2e5ae2491bb56c7b722473da481dad35ec6296b407` was independently rerun. Its output/result hash is `c8b279a8e109d6731aecf3c541f193632b6e45a7290bb7d3b06689aead3b2859`, matching the submitted evidence. It checks 8,184 pulse/permutation cases, 480 join-group permutations and 152 continuation permutations, plus endpoint/admission exclusions and an explicit simultaneous-factorization ambiguity. These finite controls supplement the full anchoring proof.

The result is an elementary consequence of the accepted reconstruction with an additional event grammar. Pair-law and BDI priors remain credited; historical priority is unresolved. No numerical estimator, conditioning guarantee, finite-number-of-loci confidence, empirical inference, original G3/G4 closure or Lean formalization is certified.
