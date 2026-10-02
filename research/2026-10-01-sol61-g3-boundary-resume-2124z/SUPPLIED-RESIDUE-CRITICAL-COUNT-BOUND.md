# An effective retained-count bound on the supplied cap-seven residue stratum

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-02 01:43 UTC.
Status: the complete hand proof passed the current head's independent challenge, including neutral-critical exclusion, effective loss/count bounds, rational-node exceptional images and finite monomial levels on critical curves. The immutable public receipt is coordinated separately. No quantifier elimination was executed for this bound.

## The finite input-dependent statement

At cap seven, fix a supplied interior residue node r. Consider any nonattained actual-closure normal form with positive drift, zero killing and exactly one positive residue at r. The enhanced criterion forces every retained strict pair to be critical for the unique covector c whose sparse polynomial F has double roots at1,r,r^2, normalized by F(0)=1.

There is epsilon(r)>0 such that EVERY strict critical pair satisfies

    p(1-q)>=epsilon(r).

This remains true if the critical locus has a positive-dimensional component. Consequently the retained list is finite and has total count at most h2/epsilon(r). For algebraic supplied r, a positive rational epsilon and an integer count bound are computable by real-closed-field decision. This is a necessary bound for the stated nonattained normal-form stratum, not a bound on arbitrary actual source realizations or input-only recognition without the supplied residue information.

## Exclusion of neutral critical sequences

Write L=c.H and use the uniformly differentiable small-p expansion on compact q intervals:

    L_p=F(q)+p T2(q)+p^2 T3(q)+O(p^3);
    L_q/p=F'(q)+(p/2)T2'(q)+(p^2/3)T3'(q)+O(p^3),
    T2=2F(q)-F(q^2), T3=3F(q)-3F(q^2)+F(q^3).

The remainders and q derivatives are uniform near either fixed interior root because every factor denominator stays in a compact positive log domain for p near zero. Saturated Descartes counting gives exactly the double positive roots1,r,r^2, with F positive on(0,1) elsewhere and F'' positive at those roots.

Suppose p->0 along critical pairs. Any interior limit q0 must satisfy F(q0)=F'(q0)=0 and hence is r or r^2. The q=0 limit is excluded by L_p->F(0)=1. The q=1 corner is excluded uniformly below.

At q0=r^2, T2(r^2)=-F(r^4)<0. The second critical equation and F''(r^2)>0 first imply q-r^2=O(p). Substitution in the first equation gives L_p=p T2(r^2)+O(p^2)<0, contradiction.

At q0=r, both F and T2 vanish doubly: F(r)=F'(r)=0 and T2(r)=T2'(r)=0 because r^2 is another double root. Here T3(r)=F(r^3)>0, since r^3 differs from1,r,r^2. The second equation gives

    (q-r)*(F''(r)+O(q-r)+O(p))=O(p^2),

so q-r=O(p^2). Then L_p=p^2 T3(r)+O(p^3)>0, contradiction. The implicit constants are fixed by r,c and the compact neighborhoods; simultaneous motion of p,q is included.

Near q=1 the exact common-factor identity is

    L=p(1-p)(1-q)^2 A(p,q),
    A(p,1)=F''(1)/2>0,

uniformly for p in[0,1]. The analytic quotient A and its q derivative are uniformly bounded on a sufficiently small compact strip. Therefore

    L_q=p(1-p)*(1-q)*[-2A+(1-q)A_q]<0

for every strict p and all sufficiently close q<1. This covers both simultaneous p->0 and p->1. It is also a special case of the previously accepted all-cap fixed-c q->1 exclusion.

If critical pairs had losses p(1-q) tending to zero, compactness of[0,1]^2 would give a subsequence with p->0 or q->1. All those possibilities were excluded. Hence the stated positive loss floor exists. No isolated-critical-point or finite-component assumption was needed.

## Effective bound for algebraic supplied r

The coefficients of c are algebraic: solve its finite linear double-root system at1,r,r^2. The critical equations H_p.H_normal=H_q.H_normal=0 are rational functions with positive denominators on the strict square. Clearing them gives the exact polynomial P_c,Q_c used in the earlier singular packet.

Enumerate rational epsilon=2^(-k), and decide

    exists0<p,q<1: P_c=Q_c=0 and p(1-q)<epsilon.

The positive-floor proof guarantees that this finite real-closed-field test is FALSE for some k. The first such value is a certified rational lower bound; an empty strict critical locus is handled automatically. This describes a finite algorithm, not an executed QE result or runtime claim.

Every retained pair has H2=-log(1-p(1-q))>=p(1-q)>=epsilon. Its total H2 loss is at most h2. For positive algebraic m2, compute an integer n>=1 with m2>2^(-n); ordered algebraic comparison terminates, and h2=-log(m2)<n log2<n. Therefore every normal form in the stated necessary stratum has fewer than n/epsilon retained factors. The conservative integer bound floor(n/epsilon) is fully computable using algebraic comparisons and rational arithmetic.

## Rational-node finite exceptional locus

For rational supplied r and a rational loss budget C>=h2, the possible critical normal forms with at most floor(C/epsilon) factors have a finite semialgebraic observation description. Let L clear the rational denominators of1-r^lambda at this cap; set e_lambda=L(1-r^lambda), a positive integer. Write A=exp(-a) and b=exp(-w/(L(1-r))). Then the observation equations are

    m_lambda=A^lambda*b^(e_lambda)*product_i(1-p_i+p_i q_i^lambda),
    0<A,b,p_i,q_i<1; P_c(p_i,q_i)=Q_c(p_i,q_i)=0.

The chosen b convention gives b^e=exp(-w R). A and b are algebraic variables in this finite description; no logarithm equality test is inserted. Enumerating the bounded integer factor counts and applying RCF therefore computes a finite exceptional semialgebraic image that contains every nonattained point in the supplied-r stratum with the promised loss budget. No comparison with exp(-C) is required: the bounded-count image is a superset, applied under the supplied C>=h2 promise. Membership in that exceptional image does NOT by itself imply nonattainment, and its complement gives an attainment conclusion only under the stated normal-form promise. General algebraic r would give algebraic irrational powers, for which this polynomial encoding is not claimed.

## Finite algebraic monomial levels, including critical curves

When r is rational, c is rational. Clear a positive common denominator to an integer vector e. On the strict square define the positive rational function

    B(p,q)=product_l(1-p+p q^lambda_l)^(e_l).

Its logarithmic gradient is the negative integer-scaled gradient of c.H. Hence BOTH ordinary derivatives of B vanish at every point of the critical locus. That semialgebraic locus has finitely many connected components, each connected by finitely many differentiable pieces of a semialgebraic path. The chain rule makes B constant along each such path. Its image is therefore a FINITE set K={K_1,...,K_t} of positive algebraic numbers, even when a component is a curve. RCF computes K directly by eliminating p,q from the critical equations and z=B(p,q), clearing positive denominator factors. A finite semialgebraic subset of the line over rational coefficients consists of algebraic points; real-root isolation returns the exact values. An empty critical locus gives K empty.

Because e.lambda=e.R(r)=0, the monomial of any critical normal form is

    product_l m_l^(e_l)=product_i B(p_i,q_i).

With the retained-count bound N_max=floor(C/epsilon), every NONATTAINED input in the stated supplied-r/loss-budget stratum must therefore lie on one of the FINITELY MANY algebraic levels

    product_l m_l^(e_l)=product_(j=1)^t K_j^(n_j),
    n_j nonnegative integers, sum n_j<=N_max.

The empty product1 covers zero retained factors. Signed monomial equations are cleared into ordinary positive algebraic products. Thus an input outside these finite levels is actual-source INTERIOR under the supplied normal-form promise: any such representation contains a noncritical retained factor, and the enhanced cap-seven rank criterion applies. This invariant can be cheaper than computing the full exceptional normal-form image, but neither computation was executed here. Being on a candidate level does not establish a critical representation or nonattainment; accidental level coincidences remain possible.

This is a fixed supplied rational-r characterization, not an exhaustive census of all unknown residual nodes. No global linear-separator inference is used. The finite-image fact uses the exact stationary master monomial on a semialgebraic critical locus; it does not require its zero-dimensionality, generic covectors or a global minimum of c.H.

## Remaining exact gap

This supplies a genuine loss floor and total retained-count bound on a singular residue branch, independent of whether its critical locus is zero-dimensional. It does not identify the supplied r from arbitrary observations, classify attainment within the finite exceptional image, or bound the unknown alternative actual source factors. Those are the next source-characterization obligations. No cap census, repeated control or additional source class is used.
