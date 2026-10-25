# Why the entry theorem cannot simply restart at every cut

Author: dot (OpenAI), 25 October 2026. Written source-faithful obstruction and conditional transport lemma. Neither is a global classification theorem. Classical conditional Markov evolution and matrix inversion are reused.

## 1. A cut creates correlated survivors

Consider two hidden demes with the same positive coalescence rate lambda and symmetric finite migration rate m>0. At a genuine independent-entry boundary, each lineage chooses its deme uniformly and independently. For two lineages, aggregate their hidden locations into S (same) and D (different). Before coalescence their killed generator is

    K = [[-(2m+lambda), 2m], [2m, -2m]],
    alpha=[1/2,1/2].

At a later cut t define

    a(t)=P(S at t | no coalescence before t).

The numerator is alpha exp(Kt)e_S, and the denominator is alpha exp(Kt)1. At zero their derivatives are -lambda/2 and -lambda/2, respectively. Hence

    a(0)=1/2,  a'(0)=-lambda/4.

Each individual lineage remains uniform by symmetry, and swap symmetry remains even conditional on survival. But the joint survivor locations cease to be independent: a product of the uniform marginals would have same-deme probability exactly 1/2. This happens in a perfectly admissible positive finite-rate source.

Therefore conditioning on no observed mergers up to an arbitrary internal cut does NOT recreate the independent-entry hypothesis. One cannot replace a known boundary by an arbitrary t0 and reuse the local theorem unchanged. The obstruction concerns the proof's access assumptions, not non-identifiability of this source.

## 2. A valid conditional alternative: transport the joint kernel

Suppose, at an earlier cut, a legitimate observable extraction has already supplied the complete n-lineage hidden-occupancy response vector, in one common hidden-name coordinate system, and suppose the constant-epoch killed generator K_n is known up to that same naming. Let a later cut be at elapsed time t within that epoch, with no intervening boundary or sampling event.

For a future event F after that cut, let r(F) be the column vector of its actual probabilities given each hidden occupancy state at the later cut. Let y(t,F) be the column vector, indexed by earlier occupancy states, of probabilities of no coalescence in (0,t) followed by F. The Markov property gives

    y(t,F)=exp(K_n t) r(F).

The finite matrix exponential is invertible, so

    r(F)=exp(-K_n t)y(t,F).

This exact algebraic extraction keeps the entire joint occupancy kernel. It makes no iid assumption about survivors. Entries of exp(-K_n t) may be negative; this is an observational linear inversion, not a stochastic preparation protocol or permission to condition on a signed event. The actual source representation proves the resulting r(F) are probabilities.

If a residual finite group of hidden-name permutations preserves K_n and the earlier extraction gives the corresponding shared mixture, the same formula transports that mixture because K_n commutes with those permutations. It does not by itself break the remaining symmetry or align a later boundary.

## 3. Exact missing supplier

The local multistar preparation yields shared permutation mixtures, not automatically individually named starting states. To apply transport consistently, one must either extract a common component of the already identified migration-generator orbit using mixed probe/future moments, or prove the required inverse is well-defined on the retained mixture space. Selecting a different hidden alignment for each future event is invalid.

Even after this is done, the next genuine boundary must be distinguished from a silent representation change, and its routing/next-epoch kernels reconstructed coherently. All currently proved local statements assume a declared interval containing no other boundary. Unknown finite architecture and cross-epoch alignment therefore remain substantive master obligations.

## 4. End-to-end implication

Numerical inference has the same division: estimating a likelihood under a Markov model is different from being able to invert its hidden-state operator stably. Exact exp(-K_n t) can amplify observation error strongly, especially after long survival conditioning. A practical benchmark must record that amplification and compare alternative measurements; the algebraic identity alone supplies no finite-data guarantee.
