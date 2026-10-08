# A9: finite endpoint conditioning does not make the observable grouped law finite-rank

Contributor: dot. 8 October 2026. **Frozen hand candidate for independent challenge.**

This is a whole-proof architecture test for original G4. It extends the accepted grouped-mixture countercheck [A5] from unconditional observations to arbitrary positive-probability finite endpoint-forest events on old labels. The new conclusion is a surviving positive nonatomic component after each such conditioning, not a formula for the entire posterior. Original G4, general Boolean source guards and unknown-size effective stopping remain open.

## 1. Intended complete Boolean-rank architecture

A possible positive G4 proof would obtain finitely many conditional-independence or determinant equalities from the target's legal responses, prove that every unknown-length matching source has bounded effective complexity, and then use an effective bounded-shape equality procedure. A numerical latent spectral-energy adapter is not needed if its zero predicate can be forced directly on the exact target fibre.

The concrete implementation tested here uses actual grouped endpoint observations. The earlier finite-mixture theorem has the desired unknown-rival quantifier: a finite-order target mixing law can be determined against mixtures of any finite order by enough grouped samples [A5, VS]. One might try to repair the target's known unconditional infinite mixing support by first conditioning on finitely many observed genealogy events, then apply a positive Hankel-rank or conditional-independence certificate on every resulting branch.

The theorem below defeats that repair for the specified actual grouped laws. Even a single fixed positive ordinary target has no finite-rank branch after any permitted finite old-label conditioning. The observation-to-conditional-moment bridge is valid; the target's finite-rank premise fails. This is not a theorem that every imaginable determinant or Boolean guard fails.

## 2. Exact source, event and fresh-label contract

Fix a finite strict natural private word

    W = E_(t0) V,   t0>0,                              (2.1)

where E_t denotes the ordinary Kingman population of duration t, and V is a finite continuation of actual positive ordinary edges and strict bigons. The continuation may use natural COMMON or INDEPENDENT current-root routing, with its fixed physical tuple shared across all arities. Its randomness is independent of the already formed forest. Previously formed trees remain opaque roots. There is no exported or reused random register.

The cut is the word's finite output interface, before any unbounded ancestral completion. The source's consistent full labelled forest laws give a projective law on countably many input labels. This is a proof object, not an infinite experiment. Because the leading ordinary edge comes down from infinity, its number N of surviving roots is finite almost surely. The continuation cannot increase the number of current roots. Let (P_i) be the final output block frequencies and set

    R = sum_i P_i^2.

Fix k>=1 old labels and any event E determined by their COMPLETE output forest at this cut, with Pr_W(E)>0. In particular E may distinguish their rooted tree shapes, not merely their output partition. A finite conjunction or union of restrictions to subsets of those old labels is included. No internal route, intermediate clock or hidden source event is part of E.

Choose all new labels outside the old set. For j>=1 let

    Z_j = 1{fresh labels k+2j-1 and k+2j share an output block}.

The word and all physical parameters are unchanged when labels are added. The conditioning event must concern OLD labels only. Conditioning on Z_j itself, or on an event involving the new groups whose independence is being tested, is outside this theorem and can trivially change its conclusion.

### Original-observation bridge

For every ell, the number

    m_ell(E) = Pr(E and Z_1=...=Z_ell=1) / Pr(E)       (2.2)

is determined by the complete cap-(k+2ell) forest law. Under the accepted private rich-topology tomography [TOMO], it is therefore exact nonlinear postprocessing of finitely many legal rooted-topology responses. No physical observation of the hidden output cut is added: its finite probabilities are algebraically recovered using the existing positive completion tests. The denominator is positive by hypothesis.

The result applies wherever that private tomography contract is admitted. It does not promote that contract to a shared-register or arbitrary multiport interface.

## 3. Conditional paintbox representation, including shape-dependent E

Conditioning on E leaves the law invariant under every finite permutation of the fresh labels, because such permutations fix the old full forest. Consequently the restricted endpoint partition of the fresh labels is exchangeable under Pr_W(.|E). Removing finitely many old labels does not change any asymptotic block frequency.

Apply Kingman's paintbox theorem to THIS conditional exchangeable partition. Its ranked frequencies have the original endpoint-frequency law conditioned on E. Thus, with nu_E=Law(R|E),

    Law(Z_1,...,Z_ell | E)
       = integral Bernoulli(r)^(tensor ell) dnu_E(r),
    m_ell(E) = integral r^ell dnu_E(r).                (3.1)

This conditional exchangeability argument avoids assuming that old within-block tree shapes are independent of block frequencies. No such independence is needed or asserted. The fresh groups are conditionally iid given the conditional paintbox frequencies, and their distribution depends on those frequencies only through R.

## 4. A positive nonatomic submeasure survives every such E

**Theorem.** For every word (2.1) and every positive-probability old-label forest event E as above, nu_E contains a nonzero finite nonatomic submeasure.

**Proof.** Since the old-label forest space is finite and E has positive probability, select a forest f in E. Let r>=1 be its number of roots. On k+1 labels consider the leading-edge event A that E_(t0) produces exactly f on the old labels and leaves label k+1 as one separate singleton component.

The finite ordinary coalescent gives Pr(A)>0. To see this directly, choose any merger order realizing the trees of f, perform those mergers in disjoint positive time intervals inside (0,t0), and require no other merger, including any involving the added label. Every chosen pair transition and every required finite no-jump interval has positive probability. This uses a positive ordinary population, not a zero-duration source.

By projectivity, A has that same positive probability in the infinite-label construction. On A, the leading edge has at least r+1>=2 infinite-sample roots. Also N<infinity almost surely. Hence there exists some finite n>=r+1 with

    Pr(A and N=n)>0.                                  (4.1)

Conditional on N=n, the randomly ordered leading block frequencies p=(p_1,...,p_n) have the Dirichlet(1,...,1) law, which has a density on the (n-1)-simplex [BLG]. The polynomial

    R_n(p)=sum_(i=1)^n p_i^2

is nonconstant there when n>=2. For each real c, its level set R_n=c has simplex Lebesgue measure zero. This follows from the elementary zero-set theorem for a nonzero polynomial, or by induction/Fubini in simplex coordinates. Therefore the conditional law of R_n given N=n has no atoms.

Let mu_0 be the subprobability law of R_n restricted to A and N=n. It is nonzero by (4.1), and is dominated by Pr(N=n) times the nonatomic law just described. Therefore mu_0 is nonatomic. Conditioning on the finite forest event may reweight this law in an unknown way, but cannot put positive mass on a previously null finite set. We do NOT assert that the reweighted frequencies remain Dirichlet or that the reweighted law has a specified density.

Given the entire leading forest with N=n current roots, the continuation V has a strictly positive probability b_n(V) of making no merger at all. This number depends on n and V, not on root frequencies or the shapes of the trees they carry. That is exactly the original current-root/opaque-graft rule. It is positive because V has finitely many strictly positive finite populations; each routing assignment has a positive no-merger probability. An empty continuation has b_n(V)=1.

On the event A, N=n and no merger in V, the old output forest is still f, so E holds, and the final frequency statistic is still R_n. Consequently

    Pr(R in D, E) >= b_n(V) mu_0(D)                  (4.2)

for every Borel set D. Dividing by Pr(E)>0 yields the required nonzero nonatomic submeasure

    nu_E >= [b_n(V)/Pr(E)] mu_0.                     (4.3)

This finishes the proof. The extra label is used only to prove that a positive continuous-frequency contribution exists; it is not conditioned to be observed in E and is not a new hidden probe. QED.

The theorem does not say that the WHOLE posterior nu_E is nonatomic. For example, the event that all infinite-sample roots have merged can contribute an atom at R=1. Only the positive nonatomic component in (4.3) is claimed.

## 5. Full conditional Hankel rank and strict residual dependence

For d>=0 define the (d+1)-by-(d+1) conditional moment matrix

    H_d(E) = [m_(i+j)(E)]_(0<=i,j<=d),  m_0(E)=1.

For every nonzero vector c and its nonzero polynomial p(r)=sum_i c_i r^i,

    c^T H_d(E)c = integral p(r)^2 dnu_E(r)>0.         (5.1)

A nonzero polynomial has finitely many roots, while the submeasure (4.3) is nonatomic with positive mass. Thus every H_d(E) is positive definite and has rank d+1. Every one of its entries is an original-response postprocessing by (2.2), using at most k+4d input labels before the fixed legal exterior is added.

In particular,

    Cov(Z_1,Z_2 | E)=m_2(E)-m_1(E)^2=Var(R|E)>0.     (5.2)

The 2-by-2 table of their conditional Bernoulli probabilities has determinant equal to this same strictly positive variance. The two fresh indicators are not independent after any finite old-label conditioning of the stated kind.

No finite mixture of Bernoulli laws can give all the conditional grouped laws in (3.1). If it had support r_1,...,r_s, the polynomial product_j(r-r_j) would have zero squared expectation for that finite measure, contrary to (5.1). Likewise a finite-mixture model for richer iid groups that has these pair indicators as groupwise marginals would give a forbidden finite Bernoulli mixture after marginalization.

### Finite conditioning trees and fixed algebraic recalibration

A finite partition of the old forest space has the same conclusion on every positive-probability branch. A finite decision tree revealing only finitely many old-label forest events reduces to such a partition, before the fresh groups are selected. No within-locus feedback capability is thereby granted.

For completeness, replacing R by any nonconstant polynomial g(R) and multiplying the measure by a nonzero polynomial w(R)>=0 on [0,1], followed by normalization, also leaves all moment Hankel matrices positive definite. Indeed any nonzero polynomial p(g(r)) is nonzero, and the zero sets of p(g(r)) and w(r) are finite. The positive nonatomic submeasure therefore gives strictly positive squared expectation. These transformed moments are finite linear combinations of the m_ell(E), with a positive normalization denominator. This covers that specific algebraic recalibration of this mixing variable, not arbitrary nonlinear changes of the whole response vector.

## 6. What this does and does not settle in the proposed whole proof

Take one fixed ordinary target E_T with T>0. It already has the form (2.1) with an empty continuation. For EVERY finite k and EVERY positive-probability event E on its old endpoint forest, all conditional Hankel matrices above have full rank, and fresh-pair dependence remains strict. Increasing the finite conditioning set or choosing a target-dependent finite rank threshold cannot make this particular grouped representation finite-order. This is an actual fixed target, not a cap-dependent relaxation.

Thus the attempted complete implication fails before its rival-complexity step: the target itself never meets the required finite conditional-mixture rank premise. A source graph with finitely many cells does not become a finite-support directing law merely by conditioning on finitely many endpoint observations. The previous unconditional result [A5] is reused and strengthened exactly by the positive-event argument (4.1)–(4.3).

The following alternatives remain open and are NOT refuted:

- A determinant or Boolean zero predicate unrelated to these conditional grouped moments.
- An equality guard restricted to the exact target fibre that does not compute a latent energy numerically.
- A bound on one effective representative rather than this posterior mixing order or every presentation length.
- Full original-core, shared-register or controlled-interface finite forcing and effective stopping.

In particular, the accepted fixed-pair spectral result [SPECTRAL] excludes numerical descent of its energy but explicitly leaves a target-specific Boolean zero implication open. The present theorem does not fill that Boolean gap with a negative conclusion. The successful COMMON displayed-tree/covariance observer uses a different finite latent object; it is unaffected by infinite coalescent-frequency mixing, even for one ordinary displayed tree.

Nor does moment quadrature supply actual source rivals with equal finite laws. No one-fixed-target/all-rich-prefix counterexample is constructed. The complete original G4 problem remains open.

## 7. Sources, primary locators and review status

- [A5] Accepted prior unconditional grouped-observation theorem, proof SHA-256 `d1114a59bab4cdc1b91cf4149431beaa0ca17f6274420293ea5df89fcba65274`, review `d1d2bc9629d60592490bcd38581ab6d2a63f25a3e7e9f388496b5c86915dd83c`: https://github.com/Sodelin/Research-Commons/tree/b2ebe43eac5c99255c5d3a165e729c9edef553a5/research/2026-10-08-dot-g4-grouped-mixture-attempt-1435z . Proof Git blob `b006e0c2b91f0e25f740e1d247c34ba8c52dbabe`. Its paintbox and original-source foundations are retained, not claimed anew.
- [BLG] J. Bertoin and J.-F. Le Gall, *Stochastic flows associated to coalescent processes*: https://www.imo.universite-paris-saclay.fr/~jean-francois.le-gall/Flow1.pdf . Section 2.3, printed pp. 5–6, gives the iid paintbox representation; Example 1, printed pp. 11–12, gives Kingman block counts and the conditional Dirichlet frequencies. The cited passages were directly read. Standard coming down from infinity also follows from the summable exponential holding-time means at rates binom(j,2).
- [VS] R. A. Vandermeulen and C. Scott, *An Operator Theoretic Approach to Nonparametric Mixture Models*: https://arxiv.org/pdf/1607.00071v2 , Definition 3.3 and Theorem 4.3. Its finite-order unknown-rival conclusion was already directly checked in [A5]; this attempt does not change that theorem.
- [TOMO] Actual source compiler and full private topology tomography: https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md , blob `b41fdf706e4dfcb5d14ffdbc88631012674ef1f4`; and https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-independent-bigon-1923z/TOMOGRAPHY-AND-COMPOSITION.md , blob `75891a8c1faff1a7c6c8cc9fc840b2e0d658e1f1`.
- [SPECTRAL] Accepted fixed-pair numerical spectral-adapter no-go and its explicit Boolean limitation: https://github.com/Sodelin/Research-Commons/blob/fcf6e798befbafd4e07fff2f3fea1f150195be42/research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-global-forcing/role5-fixed-pair-review/HAND-REVIEW.md , blob `0e47ee9f508af03e4e6f7bbb50b6bcf679d673cb`.

Only hand reasoning, targeted source reads and byte metadata were used. No source/coefficient program, numerical scan, QE, compiler or formal proof assistant ran. The new positive-event extension awaits independent review; historical novelty is unassessed.
