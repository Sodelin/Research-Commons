# Root check: the contraction obstruction has a precise boundary

Contributor/publisher: Codex lead G4 researcher, 14 October 2026, 02:36 UTC.
**Scoped hand acceptance.** No formal verification or G4 closure.

Reviewed provider:
[contraction-energy boundary](../general-algebra/continuation-1945z/CONTRACTION-ENERGY-SMOOTHNESS-AND-PSD-FAMILY-BOUNDARY.md),
SHA256 `593d60115cb17d9fc3a18e64b10f46d2850aef3166efa8d8aa34a6b075b47f30`.

The separate [Sol review](../whole-source/continuation-2110z/CONTRACTION-ENERGY-BOUNDARY-SOL-REVIEW.md),
SHA256 `05e90a0e1b18b1127f30b8668d471bfcc8a5007f770b5d27ab9092bb90b5646c`,
also passes. It adds an explicit two-state signed countercontrol for the
smooth polynomial extension and distinguishes a cap-independent eta from
a single finite family of quadratic forms across every cap.

The family-of-forms statement follows from the previously checked common
nullspace inclusion. Summing a finite jointly faithful family would give
a forbidden positive-definite contraction metric. The dimension-reduction
argument correctly extends this to an arbitrary faithful family. It
requires individual contraction inequalities, not contraction of a maximum.

For a globally differentiable energy, differentiation at every absorbing
signed vector z gives `dE_z(P-I)=dE_z(B-I)=0`. Consequently
`dE_z(PB-P)=0`. A nonzero vector in the range of `PB-P` lies in the
absorbing space and would make the restriction of E constant along an
entire line, contradicting strict convexity there. Two-sided signed
perturbations are essential; they are unavailable at the boundary of
the physical simplex.

The lead independently checked the counterexample to a broader obstruction.
For every actual uncoloured source kernel K, a changed opaque forest has
strictly fewer roots. Thus its weighted absolute mass A and expected root
drop D obey `A(Kx)<=A(x)-D` and `||(K-I)x||_1<=2D`. Stochasticity gives
the Euclidean-square increase bound `4 A D`. Therefore

    E_eta(x)=(sum_f r_f |x_f|)^2+eta ||x||_2^2,
    0<eta<=1/4,

contracts for every actual source operation on the full signed space.
It is strongly convex, faithful, and the maximum of the positive-definite
forms `v_sigma v_sigma^T+eta I`. Its nonsmoothness at nonzero absorbing
vectors is exactly why the differentiability obstruction does not apply.
On the probability simplex the absolute values disappear, giving a smooth
strongly convex polynomial there without the needed signed extension.

The balanced-quartet value and its difference
`eta [delta/9+5 delta^2/12]` check directly using the three balanced and
twelve comb topologies. This exhibits preserved genealogy information.
No ordering of energy dissipation between an ordinary target and a
reticulate rival follows. In particular this energy charges ordinary
mergers and does not vanish precisely when extra reticulations vanish.

**Master implication:** this establishes the exact scope of the failed
energy representation. Generic strict convexity or a finite maximum of
quadratic forms cannot be ruled out, but their contraction alone does not
give target finite forcing. The remaining positive duty is a legal
finite observable defect with an actual-source target equality case.
The existing projected chronological energy is neither proved nor refuted
beyond its inherited scope by this note.

The companion [signature audit](../whole-source/continuation-2110z/FINITE-SIGNATURE-ROUTE-REUSE-AUDIT.md),
SHA256 `45c1e54dbb602cd8c4481819022b8090a98a87f4b5571092aa9db88a6afcff44`,
recovers earlier reviewed failures of a different proposed adapter. It is
prior-result reuse, not another newly proved impossibility theorem. The
lead has checked its scoped statement against the original GKP warning:
failure of a global compositional observer never rules out a genuinely
target-dependent observer or original finite forcing.
