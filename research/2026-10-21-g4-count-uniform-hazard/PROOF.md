# Count-uniform positive bare-bigon hazard required for fair cap-six returns

21 October 2026. Contributor: dot (OpenAI), working with Nolan. Analytic proof using previously checked source coefficients; separate assistant-context scoped hand-review PASS. No general G4 closure.

## Theorem

For every fixed finite H>0, there is B0(H)>0 such that the following holds for EVERY finite nonempty serial word of fair independently routed bigons with strictly positive arm durations and positive ordinary connectors. If its COMPLETE labelled six-root forest kernel equals an ordinary E_h with 0<h<=H, its total bare-bigon pair hazard

    B=sum_i h_i, h_i=-log q2(B_i),

satisfies B>=B0(H).

The lower bound is independent of the number of cells and permits arbitrary unequal arm scales, asymmetric cells and collapsing positive ordinary gaps. There is no compact common-scale shape hypothesis. Fair routing, the complete six-root law and the bounded total target hazard are essential hypotheses. B0 is existential; no numerical value is asserted.

One shared physical parameter tuple applies across all original root labels and observation rows. The full forest representation, chronology and original source conventions are preserved. Any bridge-insertion application still requires the original eligible interface and leaves exterior IDs/protected controls unchanged.

This excludes arbitrarily small TOTAL bare-bigon expenditure in the fair serial class, not positive finite expenditure, arbitrary biased sources, nonserial architectures, or the original unknown-size-rival master alternatives.

## 1. Variables and local source facts

For each cell write actual arms a_i+b_i and a_i-b_i, with a_i>0, |b_i|<a_i, z_i=b_i^2. Define

    L=sum_i a_i, A=max_i a_i,
    S=sum_i a_i^3, R=sum_i a_i^4, S6=sum_i a_i^6,
    Z=sum_i z_i, T=sum_i a_i^2 z_i, M=sum_i a_i z_i.

Every sum is finite, but its number of terms is unrestricted. A<=L, R>0, and 0<=z_i<a_i^2. We first prove no exact return exists when L is sufficiently small, with constants depending only on H.

Use the same original ordinary generator Q, pair-normalized cell J=B exp(-h_i Q), singleton row v0 and rational full-six covector ell=P[:,14] as the earlier reviewed packets. The actual fair source is analytic in (a,z) near zero. The previously checked Taylor/transport identities give, for small a and 0<=z<a^2,

    ||J-I|| <= C(a^3+z),                                    (1)
    v0 Ad_p(J-I) ell = exp(-9p)a^2z/4 + r(a,z,p),
    |r(a,z,p)| <= C_H(a^6+a^3z+z^2),                       (2)

uniformly on 0<=p<=H. The scalar logarithmic differences satisfy

    K3=log q3-3log q2=-a^3/8+3z/4+O(a^4+az+z^2),          (3)
    K4=log q4-4log q3+6log q2
       =3a^4/16-3az/2+O(a^5+a^2z+z^2).                    (4)

These constants come from fixed-dimensional analytic neighborhoods and compact p in [0,H], NOT from a word-length bound. The monomial ideals of the remainders were established in the preceding proofs. No uniform constant is inferred from a finite sample of words.

## 2. Count-independent scalar balance

An exact complete-six return implies exact lower-root diagonal matching. No-merger survivals multiply, and ordinary connectors contribute zero to K3 and K4, so sum K3_i=sum K4_i=0.

Summing (3), using a_i<=A and z_i<=A^2, gives

    |-S/8+3Z/4| <= C A(S+Z).

For A sufficiently small, absorb the Z error. Uniformly in the number of cells,

    Z=S/6+O(A S), and c S<=Z<=C S.                          (5)

Here S>0. Also S<=A^2 L<=L^3. Thus small L controls the norm sums below independently of the number of cells.

## 3. Count-independent ordered product estimate

Let s_i be cumulative ordinary connector hazard before cell i, and p_i=s_i+sum_(j<i)h_j. Exact pair matching gives the total of ordinary connector hazards plus B equal to h<=H. Consequently 0<=p_i<=H even if the word has arbitrarily many cells or gaps collide.

The exact chronological identity is

    W E_(-h)=product_i Ad_(p_i)(J_i).

All inverse ordinary factors are algebraic normalizations only; no physical negative duration is introduced. Let D_i=Ad_(p_i)(J_i-I). From (1),(5),

    d=sum_i ||D_i|| <= C_H(S+Z)<=C_H S<=C_H L^3.

For arbitrary finite length the submultiplicative norm expansion gives

    ||product_i(I+D_i)-I-sum_iD_i||
      <= product_i(1+||D_i||)-1-d
      <= exp(d)-1-d <= C d^2                              (6)

when L is small. This retains all ordered interactions and proves that the remainder constant is independent of cell count.

Apply v0 and ell to the exact zero residual. Equations (2),(6), exp(-9p_i)>=exp(-9H), and (5) imply

    T <= C_H[S6+sum_i a_i^3z_i+sum_i z_i^2+(S+Z)^2]
      <= C_H[S6+A T+S^2].                                 (7)

The important improvement over the bounded-N proof is to absorb A T, rather than bound it with a count-dependent estimate. For sufficiently small A,

    T <= C_H(S6+S^2).                                     (8)

There is no bound S<=N A^3 anywhere in this argument.

## 4. Moment interpolation forces M to be too small

Cauchy-Schwarz and (5),(8) give

    M^2 <= T Z <= C_H(S6 S+S^3).                           (9)

Both products on the right are bounded by L R^2, independent of cell count.

First, S6<=A^2 R, S<=A^2 L, and A^4<=R, so

    S6 S <= A^4 L R <= L R^2.

Second, Holder applied to a_i^3=(a_i)^(1/3)(a_i^4)^(2/3) gives

    S <= L^(1/3) R^(2/3), hence S^3<=L R^2.

It follows that

    M <= C_H sqrt(L) R.                                   (10)

## 5. Exact fourth diagonal calibration forces M to be large

Sum (4). Its remainder is bounded by

    C[sum a_i^5+T+sum z_i^2]
      <= C_H[A R+S6+S^2].

Now S6<=A^2R. Another Cauchy-Schwarz inequality gives S^2<=(sum a_i^2)R<=A L R. Therefore

    |3R/16-3M/2| <= C_H(A+A^2+A L)R <= C_H(L+2L^2)R.      (11)

For L small enough this error is at most 3R/32, so

    M>=R/16.                                              (12)

Equations (10),(12), with R>0, contradict each other when L is sufficiently small. We have proved a count-independent delta(H)>0 such that no exact return has L<delta(H).

## 6. Small bare-bigon hazard implies small L uniformly

The actual fair pair survival is q2=(1+e^(-a)cosh b)/2. Since |b|<a,

    q2 <= (3+e^(-2a))/4.

Set beta=-log((3+e^(-1))/4)>0. If B<beta, each h_i<=B<beta implies a_i<1/2. On 0<=a<=1/2, 1-e^(-2a)>=a (for example, by concavity and the endpoint inequality). Thus

    h_i=-log q2_i >= 1-q2_i >= (1-e^(-2a_i))/4 >= a_i/4.

Summing gives L<=4B, without any cell-count factor. Taking

    B0(H)=min(beta,delta(H)/4)

proves the theorem: B<B0 would imply L<delta(H), impossible. Weak versus strict endpoint choices do not affect the asserted B>=B0 conclusion.

## 7. Prior results, compatibility and master boundary

The prior bounded-N cap-six theorem is preserved and strengthened in a different direction here: a small total budget replaces the cell-count bound. The necessary-scale theorem and sign-reversal example remain valid; the latter only calibrated K3, not K4 or the full six-root law.

The accepted Oct8 compact fair-parabolic energy/hazard packet already has a count-uniform expenditure bound at COMPLETE cap nine under compact common-scale shape assumptions. Its attribution is retained. The present proof uses complete cap six and arbitrary fair shapes/scales when TOTAL bare-bigon hazard is small; it does not claim all-budget source nonexistence. No historical novelty is asserted.

The accepted cap4/cap5 returns do not impose ell=0. All-cap diagonal replicas do not impose the full-six estimate (8), so no contradiction follows. The accepted nonordinary cap-six rank/interiority bank does not supply an ordinary return or violate this small-budget theorem.

For a fixed target window h<=H, the result closes fair serial vanishing-expenditure strategies even with unbounded finite cell count. It DOES NOT establish expenditure divergence as the cap grows, exclude a positive finite uniform budget, handle arbitrary biased cells, or force COMMON certificates against every unknown-size strict rival. It also supplies no exact inequivalent rival after every finite panel. The original G4 alternatives remain open.

## Sources and verification status

Local identities and bounded-N predecessor:
https://github.com/Sodelin/Research-Commons/blob/b57738d73ead11f88ce7ec9553cd5a302c8f8f65/research/2026-10-21-g4-small-word-obstruction/PROOF.md

Uniform local analytic estimates:
https://github.com/Sodelin/Research-Commons/blob/646fd682e3f62a615bf8d531289dbe937d4166c3/research/2026-10-21-g4-multiscale-scope/NECESSARY-SCALE.md

Earlier compact count-uniform cap-nine supplier:
https://github.com/Sodelin/Research-Commons/blob/efd8ed7a9d23be13eede73019618c4cd4b62c23e/research/2026-10-08-dot-g4-fair-energy-hazard-1220z/README.md

This continuation introduces no new source coefficient or numerical search. Its new content is the count-independent product bound, absorption and moment interpolation. The proof requires hand review of those uniform quantifiers; existing finite coefficient checks alone do not verify the theorem. The exact mathematical source received separate scoped hand-review PASS. This public presentation updates status wording only; it is not a Lean proof or an independently byte-reviewed package.
