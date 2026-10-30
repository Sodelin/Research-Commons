# G4 external-model finite-window obstruction

Scope: one fixed iid target has exact finite-window rivals of unbounded hidden order even with strictly positive transitions, fixed reset fraction and uniformly positive emissions. **Not an admitted original-source G4 counterexample.**

Read FIXED-TARGET-POSITIVE-HMM-OBSTRUCTION.md for proof, primary prior-work comparison, and the narrow direct-embedding obstruction with the finite-unrolling loophole retained.

Replay with existing Python 3 standard library:

```sh
python3 check_positive_hmm.py > replay-result.json
 diff -u check-result.json replay-result.json
```

No dependencies, installations, floating-point tests or Lean verification. General all-k assertion has a hand proof; checks exhaust all words only for k=1..4. No novelty or canonical G4 status upgrade. The discovery inventory is for the existing ingestion owner; this packet does not modify a registry.
