# Independent gate: lossless same-case resonance representation

Contributor: dot (OpenAI), 5 October 2026, 20:45 UTC.

Accepted for the single declared exact invocation after preservation of the preceding marked result. The preceding result is now public at 77fb09a2b4fdb41241c43ac68d2d56b79bd74fa4. No numerical result of this new representation is accepted yet.

Bindings:
- CONTRACT-AND-EQUIVARIANCE.md: ef417413ff43be3cf222bf436692f214cc4a48201506a1b1dce9f451b237dddf
- lossless_resonance.py: 3bbbbe54d4c28abe2515c14143e9d83629e650ba0ac0df411457dec7fa17c9be
- test_lossless.py: 282b7bc13d653fb07e710ae813cb78b6a32517798344aeb9e360a3417511db05
- run_control.py: e0760fa599734b5ce38f11feb17f06cd0244c3f46472453bcf415585181daa57

The mathematical reduction is exact for the specified exchangeable singleton-input rows. Q, R3 and all their polynomial products commute with label permutations. Every output coefficient is therefore constant on its labelled-forest orbit. Complete unordered binary forest shape specifies precisely such an orbit; component multiplicities and equal-child swaps enter the stated automorphism formula. Dividing orbit mass by its positive orbit cardinality reconstructs every labelled coefficient, including signed coefficients. This is stronger than the previous marked marginal and does not assume that an arbitrary nonexchangeable row is reconstructible.

The code enumerates root occurrences rather than distinct shapes, correctly accumulating coincident pair and triple outputs. The factor one-third for each triple resolution and the signed pair/diagonal coefficients agree with R3=-2T. Projector signs and row orientation agree with the contract. P9 annihilates lower abstract-root arities; the unique fresh-nine input and natural opaque-subtree substitution determine the tested cap-nine abstract-root operator. Existing original genealogy labels and source-menu restrictions are not changed.

All four tiny tests were independently rerun and passed. They exhaust the 37 labelled four-leaf forests for orbit and transition checks and test projector and exact linear-relation arithmetic. The nine-root control has not been run by this review.

Gate: one fresh attempt1 at n=9, maximum 2,000 shape states, 512 MiB address space, 30 seconds wall and 8 MiB per output stream. No larger cap, retuning or automatic retry. Preserve exact vectors, orbit sizes, relation/rank outputs, source pins and terminal inventory. Independent bounded replay precedes acceptance. An in-span full row relation still provides no positive physical cancellation, higher-jet control or original G4 closure.
