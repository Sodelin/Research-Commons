# A bounded-potential boundary for nanowire energy identification

October 17, 2026. dot (OpenAI), working with Nolan.

**Accepted scope:** hand proof and separate source-level mathematical review for the declared finite-chain model. The corrected proof is [BOUNDARY-04](BOUNDED-CLASS-IDENTIFICATION-BOUNDARY-04.md); the [independent review](INDEPENDENT-REVIEW-04.md) gives the precise checks. No solver execution, SMT decision, quantifier-elimination run or Lean verification is claimed.

The result clarifies what changes if a hard potential bound is imposed on the previously studied fixed-lead, zero-dissipation Rashba wire:

- A direct boundary-propagation estimate gives an explicit uniform open-wire inverse bound.
- For a compact admitted potential class with nonempty opposite visibility-margin classes, arbitrarily close complete energy curves occur exactly when there is an exactly equal opposite-label pair.
- An endpoint-inclusive field grid with maximum spacing h approximates the best whole-curve class separation to within h.
- For algebraically specified finite models, exact error-ball overlap has a faithful first-order real-algebraic formula. Classical effective quantifier elimination decides it in principle; practical computation has not been demonstrated.

**The remaining physical question is not answered:** the packet does not decide whether an equal-curve opposite-margin pair exists in a substantial physically admitted bounded class, or certify a positive energy separation for such a class. Parameter separation must not be mistaken for measurement separation. The fixed-lead unbounded-potential theorem remains intact; this is an explicit restricted-class analysis, not a replacement of its assumptions.

The earlier certified finite pair already gives a bounded-box obstruction at energy-error radius 0.049995 μeV and above, for a box containing its 1 eV end onsite barriers. That is an inherited consequence, not a new computation or an experimental-feasibility claim. Original Taylor lead/disorder implementation admission remains unresolved.

## Provenance and one wording correction

The original draft is preserved unchanged as [ORIGINAL-DRAFT-04](ORIGINAL-DRAFT-04.md), SHA-256 `13f6ff4c9957e0e3c4d5bf656847c0045e55dbe9ded0154338f23a9dd0c6b48e`. Its Section 6 used “Equivalently” when asserting that the two particular profiles also belong to a stated disorder box. That word could falsely suggest equivalence of the entire onsite and disorder boxes.

The accepted successor changes only that sentence. It explicitly states membership of the **two specific profiles**, and denies whole-box equivalence. Its SHA-256 is `7479c30f82f9fe63aed562e752c745483eb1fe7740572259693525981a3bf0c1`. The separate review pins that corrected version. Historical candidate headers are retained; this README records the later scoped acceptance.

## Attribution and prior results

Boundary recurrence, compactness, singular-value perturbation, midpoint error-ball logic and grid approximation are classical arguments. The exact decision reduction uses classical real-algebraic quantifier elimination, attributed in the proof. No historical novelty, new general physics principle or full inverse solution is claimed.

- [Accepted fixed-lead asymptotic theorem](https://github.com/Sodelin/Research-Commons/blob/caf7d4531c3027d19d0e899bee7129f672d1f342/research/2026-10-16-nanowire-fixed-lead-nonseparation/README.md)
- [Previously certified rational finite pair](https://github.com/Sodelin/Research-Commons/blob/b6b1f91d84e58506b9028dec1ff0c59e05317224/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-example/README.md)
- [Directed novelty comparison](https://github.com/Sodelin/Research-Commons/blob/f174251a09468254c778a1136ed5b975173fc378/research/2026-10-16-nanowire-fixed-lead-nonseparation/NOVELTY-COMPARISON-20261017.md)

The [manifest](MANIFEST.json) records exact file lengths and SHA-256 digests. It excludes itself from its digest list.
