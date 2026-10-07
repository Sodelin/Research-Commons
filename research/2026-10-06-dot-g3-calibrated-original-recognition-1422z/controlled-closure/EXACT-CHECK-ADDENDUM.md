# New exact fixed-triangle verification

Contributor: dot (OpenAI), 6 October 2026, 14:12 UTC. The author ran the frozen plan f6875309 and standard-library code 9ab0e27d after WORKING-PROOF.md was saved. Exit0, approximately0.000654 seconds, under5CPU/10wall seconds and128MiB. Complete code, actual command, output, stderr, exit and identities are preserved. No private absolute path occurs in the authored command record.

The check validates all binary degrees, acyclicity through all root-to-leaf paths, common root dominators, the hybrid child cut, a rotation system with all four leaves on one face, every strict rational edge survival, both deterministic parent paths, and the exact exclusive survivals XA=1/8 and XB in{1/2,1/4}. It recomputes the natural B affine probabilities, the Jensen defect polynomial, all six limiting A-monophyly probabilities and the forced gap1/6.

The limit profile is explicitly rational:

    11/12
    2689/3072
    6689791/7864320
    53746989349/64424509440
    18233670616137727/22166154415964160
    104039992118672301490181/127835936430807192698880
    2/3
    25/48
    5/6

The source permits free positive coalescent lengths; no equal-rate clock constraint is imported. This is a fixed graph/routing/arithmetic check, not an executed enumeration over all competing cores. The universal Jensen/full-support argument supplies the all-core NO and closure-slice failure mathematically and awaits independent review. No historical execution, source-size search, full controlled compiler, RCF or Lean run is claimed.
