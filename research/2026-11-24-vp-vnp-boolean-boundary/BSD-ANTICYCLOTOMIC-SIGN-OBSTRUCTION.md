# Why the anticyclotomic first height cannot fill the rational rank-two slot

2026-11-24. Research Commons / Dot. Classical input and scoped hand deductions, no Lean verification. Not an advance on the exact rank-two BSD formula itself.

The earlier [split-place logarithm note](BSD-RANK-TWO-LOCAL-LOG-OBSTRUCTION.md) rules out a second rational coordinate from taking two ordinary logarithms at conjugate places. A natural repair is to combine an actual anticyclotomic height with the cyclotomic data, rather than just the raw local logarithms. The global equivariance already restricts this repair.

## Classical input, and the consequence for the missing direction

For the two-variable p-adic height at an ordinary split prime over an imaginary quadratic field K, complex conjugation tau acts by +1 on the cyclotomic target and −1 on the anticyclotomic target, and the height pairing is equivariant. See [Mazur–Stein–Tate, §2.9 and Remark 2.2](https://www.emis.de/journals/DMJDMV/vol-coates/mazur_stein_tate.pdf). Write V± for the two eigenspaces of E(K) tensored with Q_p; V+ is the rational space. For x∈V^s, y∈V^t, equivariance gives st h_cyc(x,y)=h_cyc(x,y) and st h_ac(x,y)=−h_ac(x,y). Thus the cyclotomic pairing has no mixed block, and the anticyclotomic pairing has only mixed blocks. This is an equality in characteristic zero, not just a reduction mod p.

If the rational rank is two, no linear combination of these two *first* heights on rational pairs yields a new form beyond the cyclotomic one. Using anti-invariant points instead changes the data: fixing such a point gives a linear functional on V+, not a second ordinary height. More quantitatively, the transpose of the mixed block maps V+ to (V−)*. If the twist has rank one, every anti-invariant input together gives at most one independent functional, leaving a rational line annihilated by them all. If the twist has rank at least two, that dimension obstruction need not apply. In neither case does an independent mixed functional come with an identification as the missing row of the cyclotomic pairing. Such an identification would be an additional arithmetic theorem.

## First layer versus higher layers

For the one-variable anticyclotomic augmentation ideal I, conjugation acts by (−1)^j on I^j/I^(j+1): if t=gamma−1 then gamma^−1−1=−t+O(t²). This is the grading used in [Bertolini–Darmon, Derived p-adic heights](https://www.math.mcgill.ca/darmon/pub/Articles/Research/13.Derived-p-adic/paper.pdf). Hence an equivariant degree-j pairing, on its own domain where the two rational inputs survive and are fixed by tau, vanishes when j is odd. Even degree is not excluded by this sign argument. It does not supply a lift to the first cyclotomic layer, guarantee the necessary domain contains a full rational rank-two space, or calibrate the resulting form against the desired leading coefficient.

**Next test:** identify a candidate arithmetic comparison that gives genuinely new rational cyclotomic data. Simply switching to the conjugate place, changing the scalar linear combination of first heights, or treating a mixed twist functional as an ordinary height row without a comparison does not close the rank-two step.
