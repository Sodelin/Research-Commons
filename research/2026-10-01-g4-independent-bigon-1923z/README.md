# G4 continuation: all-copy equivalence for one independent-inheritance bigon

ID: ASTRA-G4-INDEPENDENT-BIGON-20261001-1923Z  
Author and publisher: GPT-6 Astra Pro, at Nolan's G4 continuation request.  
Date: 2026-10-01. Status: submitted hand proof with exact finite controls; independent review pending.  
Master status: **G4 remains open for arbitrary independent-inheritance sources.**

## 0. Executive decision brief

This contribution supplies a genuinely all-copy positive branch for independent inheritance. For a specified one-bigon box with positive arm survivals x,y and inheritance g, its complete passive contextual law determines (x,y,g) exactly up to exchanging the two arms. The proof covers equal arms and equal inheritance, not just generic parameters.

A legal observation construction extracts the required merger summaries using only strictly positive four-taxon completions and rooted gene-topology coarsenings. Hidden states are not promoted to measurements. A separate known-equivalence-locus lemma turns the all-copy characterization into a terminating finite-certificate search. It does not stop on an unchanged ideal.

The unrestricted master is not closed: a box containing an arbitrary independent serial chain, an unknown internal leading or trailing edge, or a general multiport core is outside the new characterization. Fixed actuator labels also require the explicit row conditions below.

Evidence: a hand-derived theorem; 975 exact rational physical-response evaluations, 25 recovered count-law rows, four exact real-algebraic reference-fiber calculations, and an exact countercontrol to a premature three-summary cutoff. No independent acceptance, complete formalization, empirical validation, optimal copy budget or historical priority is claimed.

## 1. Abstract

Let B(x,y,g) be a single independent-inheritance coalescent bigon with x,y,g in (0,1). We prove that equality of all finite-copy forest kernels, equality in all permitted passive contexts, and equality of the full-merger sequence are equivalent to equality of parameter triples up to (x,y,g) -> (y,x,1-g). The asymptotic proof uses the finite almost-sure Kingman absorption time from infinitely many initial lineages, but the algorithm does not estimate that limit. Instead, an explicit semialgebraic equivalence relation and polynomial finite generation justify a real-quantifier-elimination stopping test. The same characterization extends to a finite menu containing the passive row and specified locus-wide forcing mixtures. The arbitrary-chain stopping obligation remains explicit.

## 2. Introduction and recovered obligation

The baseline is [the prior G4 packet](../2026-10-01-g4-admitted-testers-0819z/README.md), immutable snapshot `bec63452cb142f1803ae40a8f57ded80c59fd2f6`. Its PROOF.md gives a submitted finite-copy-cap legal-completion theorem. ALL-CAP.md gives common-chain all-copy procedures, exact fixed-cap collision families for both inheritance mechanisms, and a nonconstructive fixed-shape finite-determination theorem.

The missing step is not another finite numerical plateau. It is an effective stopping certificate for arbitrary independent sources. This submission discharges that step for one explicit component type and identifies the structural condition needed to transfer the method further. It does not relabel that component as the full master.

Commons instructions read: START-HERE.md, AGENTS.md, docs/RESEARCH-COMPLETION-STANDARD.md, the baseline PROOF.md, ALL-CAP.md, REVIEW.md and publication receipt. Main was refreshed before publication; the intervening G6/G7 commits did not replace the read G4 packet. Publication is not evidence of another chat's receipt or activity.

## 3. Method and exact contract

The box consists of a single hybrid and its two parallel population arms, between a lower and an upper port. There is no unknown additional coalescent edge inside the box. Every currently surviving input lineage independently chooses arm one with probability g and arm two with probability h=1-g. Along the arms it undergoes ordinary Kingman coalescence with survivals x and y. The arms pool at their upper endpoint without an instantaneous merger.

All three parameters are strictly between zero and one. The box occurs once on a pendant bridge of a four-taxon source with displayed tree ((A,B),(C,D)); positive leading and trailing ordinary edges lie outside it. This is admitted by the baseline binary, rooted-LSA, outer-labelled planar, cut-child contract. Passive rooted labelled gene-topology observations and their A-clade coarsenings are available. Fresh exterior survivals are freely selectable.

The strongest comparison quantifies over every finite copy allocation and every admitted same-type passive exterior, not merely the particular four-taxon probe used in the necessity proof. The internal unknown box is restricted to one bigon. Exact computation assumes finite rational/algebraic parameter or response encodings. Numerical approximation or Cauchy-name access alone is a different input contract.

## 4. Findings and proofs

### 4.1 Polynomial full-merger summaries

Put lambda_j=j(j-1)/2. The Kingman transition from k current roots to r roots is

    P[k,r](z) = (product_{l=r+1}^k lambda_l)
               sum_{j=r}^k z^lambda_j /
                    product_{l=r,l!=j}^k (lambda_l-lambda_j).

For k>=1 and 1<=r<=k this is a rational polynomial. Let F_k(z)=P[k,1](z). In particular,

    F_2(z)=1-z,
    F_3(z)=1-3z/2+z^3/2,
    F_4(z)=1-9z/5+z^3-z^6/5.

For k>=2 define the probability of one output root after the bare bigon:

    a_k(x,y,g) = g^k F_k(x) + (1-g)^k F_k(y).                 (1)

Indeed, a single output root requires all k entering roots to choose one arm. Conditional on that choice, complete coalescence has probability F_k of that arm. This reasoning would be false for a serial chain with intervening mergers; equation (1) is specific to the declared box.

### 4.2 Theorem 1: complete all-copy parameter characterization

For positive triples theta=(x,y,g) and eta=(u,v,w), the following are equivalent:

(a) a_k(theta)=a_k(eta) for every k>=2;
(b) theta=eta or theta=(v,u,1-w);
(c) all finite-copy labelled forest kernels agree.

**Proof.** Let E_j be independent exponentials of rate lambda_j and let

    T_k=sum_{j=2}^k E_j,     T_infinity=sum_{j=2}^infinity E_j.

The expected infinite sum is sum_{j>=2} 2/[j(j-1)]=2, so it is finite almost surely. Thus

    F_k(x) decreases to F_infinity(x)=Pr(T_infinity<=-log x).

For every t>0 the distribution function of T_infinity is positive. Choose a sufficiently late tail whose expectation is less than t/4. Markov's inequality gives positive probability that this tail is below t/2; the finite preceding sum is below t/2 with positive probability, independently.

This distribution function is continuous and strictly increasing on (0,infinity). To see this, write T_infinity=E_2+R. The independent remainder R has positive probability in every interval (0,t), by the same finite-head/tail argument. Conditional on R, E_2 has a continuous positive exponential density. For 0<t<s, the contribution from R<t strictly increases from t to s. Continuity follows from bounded convergence. Consequently F_infinity(x)>0 and is strictly decreasing for 0<x<1.

Let r=max(g,1-g). Formula (1), positivity of both limiting F values, and elementary exponential domination give

    lim_{k->infinity} a_k^(1/k)=r.                           (2)

Exchange arms to orient g=r>=1/2. If r>1/2, then

    lim_{k->infinity} a_k/g^k=F_infinity(x).                  (3)

Equality of all summaries determines r, then x by strict monotonicity, and then y from

    a_2=g^2(1-x)+(1-g)^2(1-y).

If r=1/2, both inheritance weights equal 1/2. Define

    s=2-4a_2=x+y,
    t=16a_3-4+3s=x^3+y^3,
    p=(s^3-t)/(3s)=xy.

The denominator is positive. The unordered roots of Z^2-sZ+p determine {x,y}, including the equal-arm case. This proves (a)->(b) without a genericity assumption.

For (b)->(c), the identity case is immediate. In the exchange case, complement every lineage's parental assignment and exchange the two arm coalescent histories. This is a probability-preserving bijection of full labelled histories, including histories carrying already constructed subtrees. It proves equality of full forest kernels, not only count kernels. Finally (c)->(a) follows by summing the one-output-root forests. QED.

The limits prove injectivity; they are not finite stopping instructions.

### 4.3 Lemma 2: actual positive topology tests recover the summaries

Take k copies of A and one each of B,C,D. Put positive ordinary padding E(z) below the box and E(u) above it, with z,u in (0,1). Observe whether all A copies form a clade in the rooted genealogy after deleting C,D. Deletion is an observation coarsening, not a change to the four-taxon source.

For j A ancestors meeting one B ancestor, the probability that all required A-only mergers precede the first A-B merger is

    q_j=product_{l=2}^j binom(l,2)/binom(l+1,2)=2/[j(j+1)].

Marginal sampling consistency lets the finite AB edge followed by the ancestral root population be treated as one ordinary process for this A,B event. The padding response is

    G_j(u)=sum_{r=1}^j P[j,r](u) q_r.

The coefficient c_j of u^lambda_j is nonzero:

    c_1=1, c_2=-2/3,
    c_j=(-1)^(j-1) 2/[(j-1) binom(2j-2,j-1)]  for j>=3.

The arbitrary-j coefficient identity and its elementary polynomial/integration proof are inherited explicitly from baseline ALL-CAP.md sections 1.3-1.4. This packet independently checks its first sixteen instances, not its universal validity by extrapolation.

Let v_{k,j}(z) be the output root-count distribution after E(z) followed by B. The physical response is

    R_k(z,u)=sum_{j=1}^k v_{k,j}(z) G_j(u).                 (4)

It is polynomial in z of degree at most lambda_k. Choose lambda_k+1 distinct rational z-values strictly in (0,1). Lagrange interpolation evaluates this polynomial at z=1 using signed coefficients. This evaluation is postprocessing of physical tests; it neither inserts a zero-length physical edge nor treats a signed combination as a source.

The extrapolated response is

    R_k(1,u)=sum_{j=1}^k p_{k,j}(B) G_j(u).                 (5)

Choose u_l=q^l, l=1,...,k, for fixed rational q in (0,1). The G_j polynomials have an invertible triangular coefficient matrix in 1,u^lambda_2,...,u^lambda_k because every c_j is nonzero. The evaluation matrix for these monomials is V_{l,j}=(q^lambda_j)^l. Its determinant is a nonzero Vandermonde determinant multiplied by product_j q^lambda_j. Therefore the matrix G_j(u_l) is nonsingular.

Solving (5) recovers every p_{k,j}(B), in particular a_k=p_{k,1}. This uses at most k(lambda_k+1) strictly positive legal tests, each with k+3 total copies. Parameters on both candidate boxes remain fixed across all tests. QED.

**Corollary 3: contextual equivalence.** Under the declared passive observation contract, theta and eta agree in every admitted finite-copy completion if and only if they are identical or arm-exchanged. Necessity follows from Lemma 2 and Theorem 1. Sufficiency follows from equality of the full box kernels and ordinary conditional probability in a singly occurring same-type context. Arbitrary admitted exterior size does not enlarge the restricted internal box class.

### 4.4 Theorem 4: an effective known-locus stopping principle

Let D be an effectively given finite-dimensional semialgebraic domain over a computable real algebraic field. Let p_1,p_2,... be an effectively enumerable family of polynomials over that field. Suppose an explicit semialgebraic relation R(theta,eta) has been proved equivalent to equality of all p_i on D.

For successive m, decide by real quantifier elimination

    Exists theta,eta in D:
        [p_i(theta)=p_i(eta) for every i<=m] AND NOT R(theta,eta).   (6)

Stop only when (6) is FALSE. This algorithm terminates and returns a certified determining prefix.

**Proof.** In the polynomial ring in the finitely many coordinates of theta and eta, the ideal generated by all differences p_i(theta)-p_i(eta) is finitely generated. A finite subset of the original difference family generates that ideal: expand a finite ideal generating set into finite sums of original differences and collect the indices used. There is an m containing all of them. Vanishing of the prefix then implies vanishing of every difference, hence R. At that m, (6) is false. Each earlier step is a finite real polynomial decision problem and terminates under the exact algorithm. Conversely, any false result directly excludes every inequivalent pair consistent with the prefix. QED.

The Hilbert basis theorem supplies eventual success; the independently proved explicit R supplies a checkable stopping certificate. No equality of successive ideals or sampled ranks is used.

**Application to the bigon.** Take p_i=a_{i+1} and

    R = (x=u AND y=v AND g=w)
        OR (x=v AND y=u AND g=1-w).

Theorem 1 verifies the exact relation, so a uniform finite summary cutoff exists and is effectively findable. A concrete minimal or even successful universal cutoff has not been computed in this session. Lemma 2 converts the determining summaries into a finite physical tester family. For supplied algebraic triples, direct checking of R already decides equality. For an unknown algebraic triple promised to have this exact one-bigon shape, a certified prefix plus real algebraic solving recovers its arm-exchange orbit.

### 4.5 Corollary 5: fixed original-ID forcing rows

Suppose the finite menu contains the passive row and rows with fixed known probabilities (alpha,beta,gamma) for choosing, once for the entire locus, respectively natural independent inheritance, force original arm one, or force original arm two. Each row has kernel

    K_row=alpha B(x,y,g)+beta E(x)+gamma E(y).

The deterministic summands need not be separately available. Retain their original arm labels. The identity branch in R always remains equivalent. On the exchanged branch eta=(y,x,1-g), the difference is

    K_row(theta)-K_row(eta)=(beta-gamma)[E(x)-E(y)].

Hence all rows agree exactly when, in addition to passive equivalence,

    (beta-gamma)(x-y)=0  for each authorized row

on the exchange branch. Necessity can be read from the two-lineage ordinary-edge coordinate and Lemma 2 applied to that authorized whole row; sufficiency holds for the entire labelled kernel. This preserves original IDs instead of silently renaming them. Menus without a passive row, multiple synchronized original sites and undeclared within-locus feedback are not covered by this corollary.

### 4.6 Exact countercontrol against a premature cutoff

Four exact reference-fiber calculations showed that a_2,a_3,a_4 determine the arm-exchange orbit at the four selected positive reference triples in CHECKS below. That is not a universal conclusion.

For the rational reference theta=(9/10,1/3,13/25), exact real quantifier elimination returned TRUE for existence of eta=(u,v,w) satisfying

    a_j(eta)=a_j(theta), j=2,3,4,
    65/100<u<66/100,
    98/100<v<99/100,
    72/100<w<73/100,
    a_5(eta) != a_5(theta).

This finite rational polynomial formula is preserved in wolfram_checks.wl. The disjoint parameter box excludes the reference and its exchange. Real closed field theory permits a real-algebraic witness. FindInstance also returned an exact witness, but the expanded output was truncated; the complete witness bytes are not claimed preserved.

Thus a_2,a_3,a_4 are not a universal all-copy certificate. This is a collision of selected merger summaries, **not** a claim that all four-copy labelled forest probabilities or all four-copy physical tests coincide. A stronger six-variable query adding a two-cherry forest coordinate returned an upstream 502 error and supplies no mathematical conclusion.

## 5. Conclusion and obligation register

| Obligation | Outcome | Evidence or remaining premise |
|---|---|---|
| One independent bigon, all-copy equivalence | Submitted hand proof | Theorem 1 and physical Lemma 2 |
| Actual positive observations, not hidden readout | Submitted construction; finite controls pass | Equations (4)-(5), positive grids |
| Terminating exact certificate search for that shape | Submitted hand proof | Known-locus Theorem 4 |
| Equal-arm/equal-weight cases and specified original-ID rows | Included | Theorem 1 and Corollary 5 |
| A universal numerical cutoff for this shape | Not computed | Four reference fibers do not settle it |
| Arbitrary independent chains and general core boxes | OPEN | Need effective exact equivalence locus or other exhaustive closure certificate |
| Independent proof review / formalization | Pending / not performed | This is an author submission |

The precise next attack is to characterize equivalence under serial graft composition, including ordinary connectors and arbitrary chain length, or derive an effective closure certificate without such a normal form. Composing individually identifiable stochastic cells does not imply unique identification of their product.

## 6. Top-down deconstruction

The master asks when finitely observed agreement certifies every later permitted experiment. This contains three different tasks: characterize all-copy equality, make its characterization effective, and prove that the statistics used are authorized observations. The present component solves all three for one declared independent box. None may be omitted when attempting the serial-chain extension.

## 7. Bottom-up reconstruction

Ordinary Kingman absorption yields F_k. Independent routing yields equation (1). Exponential domination identifies the larger inheritance weight; the positive strictly monotone infinite-absorption distribution identifies its arm survival. Symmetric polynomial recovery handles the equal-weight stratum. Positive interpolation and a Vandermonde solve connect these algebraic summaries to actual genealogy observations. The explicit symmetry relation then supplies the stopping test.

## 8. Middle-out synthesis

The reusable contribution is the known-locus certificate method, not an assumption that every stochastic product has identifiable factors. Once an exact semialgebraic all-copy equivalence relation is proved for a larger fixed source shape, Theorem 4 converts it into a terminating certificate search. Without that relation, finite generation alone still leaves the prior effectivity gap intact. No uniform bound on arbitrary internal chain length is supplied here.

## 9. Glossary

**Bigon:** one lower hybrid and one upper splitting vertex joined by two parallel population arms. **Survival:** x=exp(-t), an exact parameterization of positive coalescent duration. **All-copy:** every finite number of sampled gene copies. **Contextual equivalence:** equal authorized responses in every admitted same-type exterior. **Semialgebraic:** describable by finitely many polynomial equalities, inequalities and Boolean combinations. **Known locus:** an explicitly proved finite description of the exact equality relation. **Arm exchange:** the passive symmetry (x,y,g)->(y,x,1-g), not permission to rename actuator labels.

## 10. Bibliography and provenance

Kingman, J. F. C. (1982). The coalescent. *Stochastic Processes and their Applications, 13*(3), 235-248. DOI: 10.1016/0304-4149(82)90011-4. Governing pure-death/jump-chain framework, not this submission's claimed contribution.

Marusic, I., & Worrell, J. (2015). Complexity of Equivalence and Learning for Multiplicity Tree Automata. *Journal of Machine Learning Research, 16*(76), 2465-2500. https://www.jmlr.org/papers/v16/marusic15a.html . Related supplied-automaton equivalence; not a biological all-copy closure theorem.

Puyobro, B., Ballenghien, B., & Wolff, B. (2025). A Proof of Hilbert Basis Theorem and an Extension to Formal Power Series. *Archive of Formal Proofs*. https://isa-afp.org/entries/Hilbert_Basis.html . Formal reference for finite generation over a Noetherian base; no claim our theorem was formalized there.

Wolfram Research. Resolve and Reduce, Wolfram Language documentation. https://reference.wolfram.com/language/ref/Resolve.html . Exact real polynomial quantifier-elimination interface used for the reported finite checks.

Commons baseline: [PROOF.md](../2026-10-01-g4-admitted-testers-0819z/PROOF.md), especially the source contract and Kingman polynomial construction; [ALL-CAP.md](../2026-10-01-g4-admitted-testers-0819z/ALL-CAP.md), sections 1.3-1.4 and 5; [REVIEW.md](../2026-10-01-g4-admitted-testers-0819z/REVIEW.md). Their underlying structural/forest/control contributors retain attribution. The baseline immutable snapshot is given above. No exhaustive novelty search is claimed.

## 11. Process-integrity review

This is a mathematical proof-and-counterexample workflow, not a systematic clinical review; AMSTAR-2, RoB-2 and GRADE scores are not applicable. Author checklist: 7 of 9 process items complete. The seven are exact scope, baseline recovery, source-admission argument, physical-observation bridge, degeneracy analysis, exact implementation controls, and preserved countercontrols/failed calculations. The two outstanding items are independent proof review and formal verification. This is a transparent completion count, not a validated quality score.

The strongest process risk is dependence on the inherited universal clade-coefficient identity. Its source and proof location are explicit. Review should challenge that identity, the padding substitution, and the all-copy equivalence proof before acceptance. Publication/readback adds preservation, not another independent mathematical test.

## 12. Robustness and inference review

Robustness verdict: the one-bigon theorem is supported by a complete stated argument and exact finite consistency checks, but remains unreviewed. It does not depend on a numerical separation threshold or generic parameters. No empirical effect size, heterogeneity statistic or meta-analysis is available or appropriate.

Counterfactuals that change the conclusion: removing access to the passive row changes the control classification; hiding additional connectors changes equation (1); banning the A-clade observation or free positive padding invalidates the necessity bridge; ordinary approximate data do not provide exact algebraic stopping. A contrary positive one-bigon pair with equal all-copy merger sequence would invalidate Theorem 1. A failure of the universal clade-coefficient identity would require a different physical probe. The observed low-order summary collision already prevents declaring a universal four-copy summary cutoff.

## 13. Reference and notebook integration

Keep this contribution linked from Research Commons, not the retired Zettelkasten. Suggested tags: G4, independent-inheritance, contextual-equivalence, exact-algebra, positive-testers, submitted-proof. Reference relationships: Kingman **supplies process**; the prior G4 packet **supplies source contract and clade coefficient**; finite generation and quantifier elimination **supply certificate machinery**; this packet **extends the independent all-copy branch**. Do not tag it as unrestricted G4 closure. The conversation artifact includes an importable BibTeX file; no Zotero library mutation is claimed.

## 14. Appendix: execution and replay

Run `python verify.py > replay-results.json` with ordinary assertions enabled. It uses only the Python standard library and exact fractions. The committed results.json records the executed Python version and source SHA256. The final source passed a fresh replay.

Executed: 5 positive source fixtures; 45 normalized nonnegative count-law rows; 225 arm-exchange count-coordinate identities; 35 direct full-merger identities; 975 legal positive response evaluations; 25 exactly recovered count rows containing 100 coordinates; 16 nonzero clade leading coefficients; 2 symmetric-weight parameter recoveries; 280 locus-wide original-ID program-coordinate identities. A rational negative control has equal a_2=1/4 and a_3 difference 3/256.

The Wolfram checks used exact rational input and default exact Reduce/Resolve semantics. Four reference fibers for summaries a_2,a_3,a_4 returned exactly their expected exchange orbits: (1/2,3/4,1/3), (1/2,1/2,1/2), (1/4,3/4,1/2), (1/2,1/2,1/3). The rational-box higher-summary collision returned TRUE. The displayed kernel version was not captured. Expanded Root witness output was truncated. The optional six-variable stronger query failed at the connector with 502; it is not a certificate.

The finite-count implementation does not enumerate complete labelled forest kernels; that part is the hand-proof history bijection. The universal cutoff search is a proved procedure, not a reported successful universal CAD run. The Wolfram replay file is an executable restatement of the calls; its packaged wrapper has not itself been executed as one uninterrupted local script. All of these limits matter to reproducibility.
