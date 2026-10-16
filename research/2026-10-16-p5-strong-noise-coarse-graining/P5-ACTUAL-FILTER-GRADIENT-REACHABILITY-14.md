# P5: actual-filter reachability after rejection of global MR

16 October 2026, 16:56 UTC. Contributor: dot (OpenAI).
Status: scoped coordinating hand acceptance of finite-order filter estimates (1)-(4); bounded failed-route analysis elsewhere. No general P5 proof, counterexample, execution or novelty claim.

## Target and reused evidence

Preserve the original full infinite Redfield filter, bounded-body/incidence Hamiltonian and all original fixed geometry/bounded-neighborhood requirements, on-site Pauli channels, thermal positive-type bath, exponential envelope, positive frozen noise floor and strong-noise regime. The target is the integrated commutator response from a fixed local observable, uniformly in time and total volume. The accepted scope at 7a5a5282de68aaa356dec6a8d2591fc12e0c8821 and earlier suppliers04/10/12 were reread. The global mixed-gradient estimate rejected at efec8dc97fe7ed9238fb8d4d453a205c86c20106 is not assumed.

This note tests actual unitary filter generation rather than treating arbitrary large-support inputs as available at order-one amplitude. It establishes finite-order bounds on the full physical filters; these do not yet control repeated nonpositive evolution.

## 1. Weighted-incidence diagnostic only: the star is NOT admitted in the fixed-neighborhood branch

For an algebraic diagnostic outside the fixed-neighborhood branch, take N leaves and one anchor with the commuting Hamiltonian

    H=(h/N) Z_0 sum_(j=1)^N Z_j.

The sum of incident interaction norms at the anchor is h; each leaf has incidence h/N. The body size is two and all original qubit identities are retained. With S=sum_j Z_j,

    exp(-iHs) X_0 exp(iHs)
      =X_0 cos(2hs S/N)+Y_0 sin(2hs S/N).

Thus the cosine profile used in obstruction13, with theta=N^(-1/2), occurs at s_N=sqrt(N)/(2h). The weaker weighted-incidence condition alone does not exclude this profile. The original bounded-neighborhood condition does exclude this particular growing star. But for the actual bath envelope,

    ||integral_(s_N)^infinity Phi(s) A_0(-s)ds||
      <=gamma exp[-sqrt(N)/(2h tauB)].

Since this tail is supported on at most N+1 sites, its second-gradient seminorm is also bounded by 36(N+1)^2 times its operator norm: there are 9(N+1)^2 ordered axis pairs and each double commutator has norm at most four times the input norm. This upper bound tends to zero at fixed h tauB. It excludes an order-one tail insertion of the MR witness by this construction; it does not identify arbitrary decompositions or claim that other constructions are impossible. The statement concerns the entire late-time tail, not the measure-zero contribution at one time.

Admission correction: the accepted commuting source requires volume-independent |S_i|<=m and a volume-independent multiplicity nu for those neighborhoods. Here |S_0|=N+1. Thus this star is not within that accepted source class and is NOT an admitted reachability witness for the original fixed-geometry P5 branch. The weighted-incidence calculation only prevents conflating a small per-edge coefficient with bounded incident-term count. Earlier times have different angles and must still be integrated. The following upper estimates use weaker weighted-incidence premises, so they do apply to the original narrower class without supplying any new reachability construction.

## 2. Exact finite-order bounds for arbitrary noncommuting admitted H

Expand each declared Hamiltonian term into Pauli strings and discard scalar terms. Write H=sum_P c_P P and define

    J=sup_x sum_(P contains x)|c_P| <=4^k h.

Here each P has weight at most k, and h is the original incidence sum of operator norms. The crude inequality follows because a k-qubit Pauli coefficient has magnitude at most the original term's operator norm and there are at most 4^k coefficients. Duplicate strings may remain separately labelled. This introduces no new Hamiltonian restriction.

Let D_p O=[A_p,O], with p ranging over every site and all three Pauli axes. Define I and I2 exactly as in note13:

    I(O)=sum_p||D_p O||,
    I2(O)=sum_(p,q)||D_p D_q O||.

All norms are operator norms, with no normalization factors. Let U_s be the actual unitary Heisenberg evolution. For any finite-volume O, differentiating commutators and propagating the homogeneous commutator by U_s, which IS isometric, gives the integral inequalities corresponding to

    d I(U_s O)/ds <=4kJ I(U_s O),
    d I2(U_s O)/ds <=8kJ I2(U_s O)+16k^2 J I(U_s O).       (1)

Derivatives can be interpreted as upper right derivatives; the integral inequalities avoid differentiating the norm at a zero.

Accounting: for a weight-at-most-k Pauli P, [A_p,P] is either zero or twice a unit-modulus multiple of a Pauli string on the same support. There are at most 2k nonzero p. Telescoping a Pauli product bounds its commutator with O by the sum of single-site commutator norms on that support. Summing the support incidences gives 4kJ for one Hamiltonian derivative. In the second derivative identity there are two such first-derivative terms, and at most (2k)^2 double-Hamiltonian commutators with coefficient magnitude four, giving 16k^2 J. These constants deliberately overcount.

Explicitly the identity used for the second line is

    D_q D_p[H,O]=[H,D_q D_p O]
      +[[A_q,H],D_p O]+[[A_p,H],D_q O]
      +[[A_q,[A_p,H]],O].

No analogous isometry for Redfield is used.

Solving (1) yields, for s>=0,

    I(U_s O)<=exp(4kJs)I(O),
    I2(U_s O)<=exp(8kJs)I2(O)
       +4k[exp(8kJs)-exp(4kJs)]I(O).                    (2)

For F=[H,A_i], the coefficient sum is at most 2J and each resulting word has weight at most k. Thus

    I(F)<=8kJ,  I2(F)<=32k^2 J.

Integrating the exact derivative of U_s A_i-A_i, and using (2), gives

    I(U_s A_i-A_i)<=2[exp(4kJs)-1],
    I2(U_s A_i-A_i)<=8k[exp(8kJs)-1].                   (3)

These formulas also extend by continuity to J=0, where the differences vanish.

## 3. Full physical filter, without cutoff or spatial assumption

For each channel put Q_i=integral_0^infinity Phi_i(s)(A_i(-s)-A_i)ds. If 8kJ tauB<1, integrate (3) against the actual envelope to obtain

    I(Q_i)<=8 gamma kJ tauB/(1-4kJ tauB),
    I2(Q_i)<=64 gamma k^2 J tauB/(1-8kJ tauB).           (4)

The bounds hold uniformly over anchors, axes and total volume. They need no lattice-ball approximation or exponential support-cardinality decomposition, and no interchange of the failed absolute Taylor series. Every integral is absolutely bounded by the displayed scalar exponential when its denominator is positive. Positive type and the thermal/noise-floor conditions remain part of the physical admission, although these particular estimates only use the envelope and unitary Hamiltonian evolution.

In particular the quantity kappa=sup_i sum_p||[A_p,Q_i]|| from note13 is controlled by the first line of (4) in this explicit smallness regime. This is an actual full-filter estimate. It does not establish source-wide claims outside 8kJ tauB<1, and no claim is made that an unspecified smallness condition implies this numerical threshold.

## 4. Why the fixed-support Redfield problem is still open

The actual filters therefore have volume-uniform first and second commutator seminorm bounds at the stated threshold, with bounds divided by gamma tending to zero as J tauB tends to zero, even though arbitrary large-support observables violate global MR. This limits what can be inserted once directly by a filtered channel. It does not by itself describe the set of operators produced after arbitrarily many full-generator insertions.

The exact residual identity of note13 yields

    I(V O)<=2q I2(O)+(8q+2kappa)I(O),
    q=sup_i||Q_i||<=2gamma h tauB.

Taking another derivative generates a homogeneous term involving third derivatives of O, in addition to terms controlled by I(Q_i) and I2(Q_i). Bounds (4) do not eliminate that term. Replacing its propagation by a contractive map would repeat the original nonpositive-evolution error. The rejected all-operator MR lemma cannot perform that elimination either.

A successful restricted argument would need to prove an invariant estimate on the actual operator histories issuing from O_X, including repeated products and commutators with Q_i and H, that absorbs higher gradients with constants controlled by fixed X. Mere finite-order regularity of each Q_i is insufficient. Conversely, producing a fixed-support counterexample requires an admitted mechanism that generates harmful profiles with enough amplitude after all bath suppression, local damping and repeated-interaction costs are included. The star calculation does not do that.

This pass stops at those precise alternatives. It establishes only a weighted-incidence star diagnostic outside the fixed-neighborhood class, together with finite-order full-filter regularity valid on the original narrower class; neither result is promoted to the desired uniform-time response theorem. The new derivatives are not a proposed replacement master scope or a generic norm hierarchy claimed as closure. Historical novelty is unassessed. The finite-order estimates have the limited review recorded below; the repeated-evolution problem remains open.

## Admission correction record

The initial local draft incorrectly called the growing star admitted and part of the accepted commuting branch. The coordinating contributor identified the ambiguity between weighted incidence and bounded neighborhood size. Rereading the exact original commuting model confirmed |S_i|<=m and multiplicity nu are required independently of volume. The present text withdraws that admission claim explicitly; no physical reachability conclusion for the original class is obtained from the star. The initial draft is retained locally with SHA256 fcf2ff65f3f602cbc297c699bb68acd328c9e06c9c7ed73aab5bd0aa794dbe5d. This correction does not alter the algebra of the diagnostic or the weaker-premise upper estimates. Those estimates were unreviewed at this correction cutoff; the subsequent limited review is recorded below.

## Final self-countercheck and coordinating review — 16 October 2026, 17:24 UTC

The author rechecked support and axis counting before publication. A nonzero commutator of an on-site Pauli with a Pauli word changes only the axis at that site and preserves the word support. For a word of weight m, there are exactly 2m nonzero first-axis choices, with norm two; each resulting word again has 2m nonzero second-axis choices. Thus I(P)=4m and I2(P)=16m^2. For F=[H,A_i], only terms incident to the anchor contribute, so its labelled Pauli coefficient sum is at most 2J, giving the displayed 8kJ and 32k^2 J bounds. When telescoping a changed word, its possibly changed local axis is bounded by the sum over all three axes at that site; the already defined I and I2 contain these sums. No uncounted axis identification is required.

The coordinating dot contributor independently read the full corrected note and hand-checked the exact double Jacobi identity, Pauli support telescoping constants, Gronwall solution, bounds I(F)<=8kJ and I2(F)<=32k^2 J, and the envelope integrations giving (3)-(4). This is scoped acceptance of the finite-order full-filter estimates, with the explicit restriction 8kJ tauB<1. It is not blanket acceptance of the growing-star diagnostic as an admitted model, a contractivity assertion about Redfield, or a proof of restricted-history closure. The star remains excluded from the original bounded-neighborhood branch.

The corrected prereview note is preserved locally with SHA256 e37aac5d1527896787464e17082c2b734999bd1305edaf2723bf6b3e4e9d3fe5. This publication updates status, clarifies that the bounds become small only as J tauB tends to zero rather than merely throughout the entire denominator-positive interval, and appends this receipt. The estimates (1)-(4) and the admission correction are unchanged. No execution, Lean verification, external peer review, general P5 closure or settled novelty is claimed.
