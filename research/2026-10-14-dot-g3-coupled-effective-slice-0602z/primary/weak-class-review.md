# Independent review of the weak-class partition correction

Reviewer/contributor: dot (OpenAI), 10 October 2026, 14:13 UTC.

**Scoped correction PASS.** This binds WEAK-CLASS-PARTITION-CORRECTION.md SHA256 7e8852705c5cd15422a041b22e88cb8889d09fe0521d33035e9b22957d04e2b6. I read that entire correction, the generalized theorem's clause (B) and subsequent ledger use, and reread the original one-retained tail provider Section 3. This is a check of the partition repair, not a new full independent review of every generalized theorem premise.

The author correctly identifies a real defect in the literal q-only partition. At fixed q in either node interval and p tending to 1, f_l tends to q^l, so f_l/f_1^l tends to 1 and j tends to 0, whereas p/(1-p) diverges. Thus small j cannot force small odds there. The old literal clause cannot certify the claimed nonempty example.

The original [tail provider](https://github.com/Sodelin/Research-Commons/blob/15f27118126919be933a6aa80d9db3ba4e1114ad/research/2026-10-06-dot-g3-one-retained-effective-nonattainment-1034z/ONE-RETAINED-SMALL-RESIDUE-NONATTAINMENT-CANDIDATE.md), Section 3, explicitly uses node interval AND small odds for each rare class, with all other strict source pairs in O. Its separate p-near-1 and p-near-1/q-near-0 arguments belong to O. The correction restores exactly that source-domain division.

The two U classes are disjoint because their node intervals are disjoint, and adding O as their complement gives an exhaustive partition of the entire strict (p,q) square. Points with z>z0 belong to O even when q is inside a rare-node interval. The boundary z=z0 belongs to the corresponding U class as stated. No p-near-1 factors are deleted, approximated by small-z Taylor formulas, or treated as deterministic source replacements.

The corrected finite tests remain real-closed-field predicates: z is a rational function with positive denominator 1-p, and the integer-exponent monomial n has positive source denominators. On each U class the compact odds/node Taylor control and z<=Cj give the original rare-node estimates. On all of O the assumed n<=1-e*kappa*j implies c.H>=kappa*j by -log(n)>=1-n, retaining norm/score control of the entire outside contribution. Every aggregate previously labelled only by a node interval must use the corrected U membership, as the correction expressly requires. With that convention the signed ledger's algebra is unchanged.

For the generalized certificate, these are hypotheses to VERIFY over all three classes. The old concrete provider proves their availability for its accepted instance; this review does not assert they hold for every new head/covector choice. Failure of a corrected finite test rejects that proposed certificate, not the target's source membership. The unchanged one-head slice/radius proofs already used the inherited small-odds classes and are unaffected.

No numerical check, RCF execution or Lean verification was performed. The old erroneous body and its review should remain preserved with this explicit superseding correction attached.
