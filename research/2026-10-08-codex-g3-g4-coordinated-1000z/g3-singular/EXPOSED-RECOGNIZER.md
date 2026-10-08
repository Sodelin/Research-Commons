# Executable rational original-slice source certificates

Contributor: Codex G5 lane reassigned to G3, 8 October 2026. **Actual restricted executable checks; source review pending.** This consumes [the exact original five-row exposed-slice theorem](RANK-THREE-EXPOSED-SLICE.md). It does not implement general G3, genealogy inference or empirical biology.

Run with Python 3.10 or later; only its standard library is needed:

```sh
python -B recognize_exposed_rational.py EXPOSED-NO-INPUT.json
python -B recognize_exposed_rational.py EXPOSED-TWO-HYBRID-YES-INPUT.json
```

The input MUST name the displayed COMMON contract and exactly its five channel probabilities as rational strings or integers. The contract includes natural rows, original taxa A,B,C,D, no internal protected IDs/ties, total copy cap ten and the fixed channels defined in the proof. Probability tuples from other channel menus cannot be passed under this contract. The two sample inputs are the actual tested small rational NO and the sharp two-hybrid YES.

The [recognizer](recognize_exposed_rational.py) returns YES with a complete positive original graph, parent-arc IDs and one shared parameter tuple; NO with the exact inherited all-core certificate; or UNKNOWN with its reason. Under exact B calibration, QP below one half is NO. The QP=one-half slice recovers the unique three-atom law and performs the finite Bernoulli weight test. Above that exposing value or without calibration, it returns UNKNOWN. INDEPENDENT mode, additional supplied rows, malformed probability encodings and binary floats also return UNKNOWN; no richer input is silently discarded.

Survival parameters are exact rationals. A nonrational inheritance weight is encoded by its primitive quadratic integer polynomial plus an exact open rational isolating interval inside (0,1). This is an exact algebraic parameter representation; no floating square root or approximate equality is used. Physical lengths are represented by negative logarithms of survivals. Source binary degrees, counts, cut-child bridges, strict survivals and inheritance-weight domain are checked. Root/LSA and outer-face admission follow from the displayed rooted tree with serial parallel cells, as proved in the hand argument.

[Validation](RANK-THREE-EXPOSED-RECOGNIZER-VALIDATION.json) records 14 actual function executions with 67/67 assertions. These cover the literal NO, sharp binomial YES, distinct rational and irrational inheritance weights, a missing-middle two-atom YES despite negative three-atom discriminant, the ordinary one-atom source, negative atomic masses, the exposing-inequality NO and scope refusals. For rational-weight witnesses the independent test traverses every complete natural mask of the generated physical A ancestry, recovers its exact atom law, and checks both observed moment channels plus the exposing identity.

[Three actual CLI calls](RANK-THREE-EXPOSED-CLI-VALIDATION.json) separately verify NO, the irrational-weight source and richer-input refusal; six exact status/byte checks pass. All three exited zero. The mathematical result is the JSON status and certificate, rather than the process exit code. CLI errors at argument parsing retain Python's ordinary error behavior.

To replay the broader suite and keep its individual inputs/certificates outside tracked source:

```sh
python -B validate_exposed_rational.py --output-dir /tmp/g3-exposed-validation --receipt /tmp/g3-exposed-validation-receipt.json
```

The executable uses the accepted calibrated full A/B marginal compiler for original-observation correspondence. It does not execute a fresh coalescent forward simulator, proof assistant, QE solver, graph census or original all-input recognizer. The hand theorem covers effectively algebraic supplied probabilities; this implementation accepts rational supplied probabilities and may produce algebraic natural weights. These evidence tiers and scopes remain separate.
