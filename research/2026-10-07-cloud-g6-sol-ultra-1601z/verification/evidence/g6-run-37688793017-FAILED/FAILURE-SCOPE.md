# Actual partial repair result

Run 37688793017, frozen `3767c9daa16ecdda851f16295973ceb250ec1de0`: overall FAILURE. The failed residual/principal modules remain excluded even where their recovery output prints standard axioms.

Of 158 command receipts, 156 exited zero; 153 custom modules passed. The actual named audit has 201 reports (139 G6, 47 G3, 15 G5). The full successful-module inventory contains 3,711 owned declarations / 2,384 theorems, raw 5,478,914 bytes, SHA256 `7c749e559613aac527f7cf5e59c632b4a29b52af0198de39ff117c5dfc4bc20a`, with zero owned axioms, nonstandard rows or missing modules. All 155 frozen source hashes and 157 non-cache stdout hashes match; complete payload, audit sources and all 157 stdout hashes also match the authenticated Actions ZIP artifact.

Accepted additions: CompleteCalendarBinReadout SHA329abd02 has 14 named/19 owned; ActualTailBinRow SHA790d2284 has 5 named/5 owned; UpperMeanCommon SHA03bfc2b5 has 11 named/30 owned. Their precise contracts are described in README.md. They do not imply the failed principal or residual consumers.

ResidualProgram failed at183 because a multiline application was placed after a same-line case arrow, causing parsing/type inference failure and an unprovided boundary alternative. CompleteCalendarJointLaw failed at54 because its toMeasure lemma lacks the already proved local probability instance, at182 because map_congr cannot syntactically match the composed lambda and local measure aliases, and at201 because the implicit Code binder is unconstrained for SFinite inference. These are actual diagnostics, not a receipt for a proposed repair. All original author source bytes and both failed source inputs are preserved unchanged.

The CLI watcher encountered401, so the completed run was retrieved through the authenticated GitHub connector and its authenticated artifact digest, with official public metadata readback. `connector-job-original.log` preserves the exact decoded job log; `connector-artifact-provenance.json` explains the limited prefix normalization in actions.log and independent artifact equality checks. No duplicate job or input change occurred.
