# Direct coin-bias control from the full seven-root band

Stable key G3-FULL-BAND-BIAS-01. Existing G3 owner,24October2026UTC.
PROVED BY HAND at the scope below; author self-review complete.
Independent correctness review and Lean formalization not performed.
No new source/tuple/coefficient/model/solver/native execution.

## 1. Statement on the original full-forest fibre

Use actual finite strict equal-arm private words K, arbitrary natural
coins and arbitrary relative cell scales/finite counts. Preserve original
CURRENT-root routing and opaque grafting, SAME tuple and chronology.
Retain the unchanged active conditions

    K_COMMON=E(c), b2I(K)=c^(3/4), c=2^(-1/m),
    [K_I,S(t)]=0 through the COMPLETE forest cap7,
    H=-log c, h=-log t, 0<h<H/4,

    S(t)=E(t) B(t/(2-t),t/(2-t),1/2) E(t^2*(2-t)).

E(v) denotes ordinary SURVIVAL. Every cell has common arm survival
q_i=exp(-a_i), actual parent0 coin g_i, and

    v_i=g_i*(1-g_i), beta_i=(2g_i-1)^2,
    W=sum_i v_i*beta_i^2*a_i^3, L5=sum_i v_i*a_i^5.

There exist fixed effective H0,h0,C>0 such that EVERY such word with
0<H<=H0 and0<h<=h0 satisfies

    W<=C*(L5+H*h^4).                                  (1)

No coin margin, homogeneous-cell promise or count bound is assumed.
The original COMMON budget gives a_i<=H automatically; a sufficiently
large FIXED m is already permitted by AG-Pair.

The same bound controls the completed transverse-source majorant

    sum_i v_i*(beta_i^2*a_i^3+beta_i*a_i^4+a_i^5)
       <=C*(L5+H*h^4).                               (2)

The earlier MATCHED-BAND-BIAS-CONTROL bound retained an additional prefix
energy E_a on the right. Equation(1) REMOVES that dependency by using
full-forest information outside R. It does not bound L5 in h, prefix
energy, V_h or the phase/index. Original AG-Pair and total G3 remain
UNPROVED; this component is not a newly narrowed completion standard.

## 2. Exact predecessor/successor comparison

REUSE the OLD accepted all-cell/bilinear identities and reviews at
Commons8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6. Their exact complete
paths/hashes and acceptance scopes are in the immediate successor

[FULL-SEVEN-BAND-ORIENTATION.md](https://github.com/Sodelin/Research-Commons/blob/a0606d481186c000b106ee717a572e1e7e724743/research/2026-10-24-g3-asymptotic-root-grid/FULL-SEVEN-BAND-ORIENTATION.md),
14246B/SHA00332ce1296773cbc59566e511502f0851fa61bc593bb8312e3a9a5086aa56ee,
whose complete body was read. It supplies BOTH independent7-to4
coordinates and their SAME positive actual transport. Its ratio
identification consequence is homogeneous FAIR only; we do not extend
that consequence to biased cells.

The older [matched-band bound](https://github.com/Sodelin/Research-Commons/blob/dce8b2e343012eb1042719a89e9b8c14a1e86930/research/2026-10-24-g3-asymptotic-root-grid/MATCHED-BAND-BIAS-CONTROL.md),
10293B/SHAf2b83617627f4ecff7dd926f31fde871982e44433efbe942287f184a53113517,
was read COMPLETE. Its R-normalized mixed-band equation has prefix
terms and yields W<=C*(L5+E_a+H*h^4). It stays TRUE. The new argument
acts on ONE full band and introduces no such prefix terms.

COMPLETE OLD METHOD-COMPARISON-AND-SOURCE-STATE.md6918B/
SHA7da5c426153438a70513dc7bf703f5ab77630831d4196bd6e83f718c4f75470f
and accepted interior-coin source addendum7641B/
SHA81de27ab78b4bf8b8889d2b8a7005194264b831396a50ac0d71076899ac660b6
were also read. Their selected R state and general source jets are REUSED,
not a missing append engine or new source calculation. The proof below
displays the needed fair quartic cancellation directly on the FULL band.

Relevant current/archive aliases were compared before this write.
This is a bounded predecessor/successor comparison, not a historical
priority or exhaustive absence claim. The actual R-only phase-flexible
counterfamily remains PROVED; no R-only phase inference is revived.

## 3. A full-band functional and its exact BARE-cell EPPFs

In the notation of the full-band predecessor define for ANY actual
prefix K

    Psi7(K)=S7(K)-(2/3)*L1(K)=2*w7(K)-u7(K),           (3)

using the per-labelled triple-plus-cherry and four-comb top coefficients
of P7 K P4. This is a LINEAR functional of that SAME band, not an added
observation. The original completed caller supplies the complete forest
law; spectral postprocessing adds no latent channel.

For ONE bare cell B the OLD relation L1(B)=-11*d7(B)/12 gives

    Psi7(B)=S7(B)+(11/18)*d7(B).                      (4)

This last equality with d7 is NOT applied to a whole word.

Let A_n=3*p_n(2,2,1^(n-4))-2*p_n(3,1^(n-3)), so d_n=A_n/(2n-3).
The OLD exact formula S7=-d6/2+e7, with its NONZERO extra e7, gives

    Psi7(B)=(A7-A6)/18+e7.

One-label partition consistency, on that SAME bare source, says

    p6(2,2,1,1)=2*p7(3,2,1,1)+2*p7(2,2,2,1)+p7(2,2,1,1,1),
    p6(3,1,1,1)=p7(4,1,1,1)+3*p7(3,2,1,1)+p7(3,1,1,1,1).

Thus A7-A6=2*p7(4,1,1,1)-6*p7(2,2,2,1).
Substituting the exact e7 gives the compact identity

    Psi7(B)=[6*p7(3,2,1,1)-6*p7(2,2,2,1)
                         -p7(4,1,1,1)]/18.          (5)

Every p is ONE specified set-partition probability, not orbit mass.
No EPPF is fitted separately; all come from the same original cell.

## 4. Uniform all-coin source inequality

Put B=B(exp(-a),exp(-a),g), v=g(1-g), beta=(2g-1)^2.
All three probabilities in(5) require exactly THREE binary mergers.
Let r_j=g^j+(1-g)^j. Their cubic coefficients follow by counting
compatible histories and keeping the initial current-token routing:

    [a^3]p7(3,2,1,1)=(3/2)*r3*r2,
    [a^3]p7(2,2,2,1)=r2^3,
    [a^3]p7(4,1,1,1)=3*r4.

There are9,6,18 compatible ordered histories respectively, each with
leading factor a^3/6. Their monochromatic-block routing probabilities
are r3*r2,r2^3,r4; singleton factors are1. Therefore(5) gives

    [a^3]Psi7=(3*r2*r3-2*r2^3-r4)/6
             =v*beta^2/6,                            (6)

using r2=1-2v,r3=1-3v,r4=1-4v+2v^2. Lower coefficients vanish.

We also need the FAIR degree-four coefficient to vanish. Here is a
complete short history calculation, rather than an R-only inference.
Conditional on each final block being monochromatic at g=1/2, its color
is independently fair. This event has probability1/8 for ALL three
seven-token/four-block partitions in(5).

After j mergers let k_l(j) be the numbers of CURRENT roots still inside
each eventual block. The conditional expected colored holding rate is

    (lambda_(7-j)+sum_l lambda_(k_l(j)))/2.

A three-merger path contributes at degree4 the NEGATIVE of the sum of
its four holding rates, divided by24. The universal half-sum of the
ordinary rates is(21+15+10+6)/2=26. The remaining internal sums are:

| Partition | Histories | Sum over histories of sum_(j=0)^3 sum_l lambda_(k_l(j)) |
| --- | ---: | ---: |
| 3,2,1,1 | 9 | 66 |
| 2,2,2,1 | 6 | 36 |
| 4,1,1,1 | 18 | 180 |

For3+2, the triple's two events and the cherry's event have three
interleavings, each with three internal triple histories. Their internal
sums are7,7,8, giving3*(7+7+8)=66.
For three cherries every path has sum3+2+1=6, giving36.
For a four-block merger every path has sum6+3+1=10, giving180.

Both weighted sums in(5) cancel EXACTLY:

    6*9-6*6-18=0,
    6*66-6*36-180=0.

Hence

    [a^4]Psi7(B(exp(-a),exp(-a),1/2))=0.              (7)

The original finite source entries are polynomials in q=exp(-a),g.
Psi7 is symmetric under g<->1-g and vanishes at deterministic endpoints
g=0,1, where B is ordinary. Divide the finite polynomial by v BEFORE
taking analytic remainders, so the quotient extends to BOTH endpoints.
Equations(6)--(7) now imply, uniformly for0<=g<=1 and small a>=0,

    Psi7=v*[beta^2*a^3/6+beta*A(g)*a^4+a^5*R(a,g)],  (8)

with fixed effective bounded A,R. Symmetry and the fair zero give the
beta factor in the quartic coefficient. Uniformity follows from the
finite polynomial source and compact q,g domain, not extrapolation
from an interior-coin estimate.

Young's inequality bounds |A|*beta*a^4 by
beta^2*a^3/12+C*a^5. Thus fixed effective constants give

    Psi7(B)>=v*beta^2*a^3/12-C*v*a^5,                (9)
    |Psi7(B_fair)|<=C*a^5.                         (10)

No claim that Psi7 itself has one sign on all cells is made. The negative
fifth-order remainder is retained. This is not a global PSD cocycle or a
positive synthetic-kernel admission theorem.

## 5. Full commutation bounds the endpoint without prefix energy

The completed exact word recurrence on this ONE band gives

    Psi7(K)=sum_i omega_i*Psi7(B_i),
    omega_i=product_(before i)b7 * product_(after i)b4. (11)

Both factors use the actual complete original chronological word. Let
c(f) be a factor's COMMON pair survival: q_i for an equal-arm cell,
and its ordinary survival for an ordinary edge. Then

    product_f c(f)=c,
    c(f)^lambda_r<=b_r(f)<=1,
    c^21<=omega_i<=1.                              (12)

For a cell the lower bound is immediate from its exact no-merger sum:
each routing term has exponent lambda_j+lambda_(r-j)<=lambda_r.
No COMMON clock or conditional register is reset to obtain it.

Let k_r=b_r(K),s_r=b_r(S(t)). The same full-band commutator equation
as in the predecessor gives

    Psi7(K)=[(k4-k7)/(s4-s7)]*Psi7(S(t)).             (13)

The no-merger law is nonincreasing with current-root count, and(12)
implies k7>=c^21. Consequently

    0<=k4-k7<=1-c^21<=21H.                          (14)

For the KNOWN reference, its fair arm duration is
a_*=log(2*exp(h)-1)=2h+O(h^2). The two bookends have total ordinary
duration2h+O(h^2), and the fair cell's first ordinary duration is
a_*/2=h+O(h^2). Hence

    s_r=1-3*lambda_r*h+O(h^2),
    s4-s7=45h+O(h^2)>=c0*h                          (15)

for a fixed effective h0. By(10), ordinary pad scaling on P7/P4 and
a_*=O(h), we have |Psi7(S(t))|<=C*h^5. Equations(13)--(15) give

    |Psi7(K)|<=C*H*h^4.                             (16)

No unknown b_r(K) has been set to a fractional reference power.
No prefix coordinate, trace estimate, ordinary frozen exterior or
energy bound entered this endpoint estimate.

## 6. The bias bound and the exact remaining gap

Apply(9) term by term in(11), using the SAME positive weights and(12):

    Psi7(K)>=c^21*W/12-C*L5.

Combine with(16). Since H<=H0 makes c^21 bounded below by a fixed
positive constant, this proves(1) uniformly in every coin/scale/count.

Finally beta*a^4<=sqrt((beta^2*a^3)*(a^5)).
Cauchy--Schwarz across cells gives

    sum v_i*beta_i*a_i^4<=sqrt(W*L5)<=(W+L5)/2.

Together with(1), this proves(2), the precise majorant already used in
the completed compensated-source jump proof. Its old source identities,
reference forcing and trace bounds are reused without another run.

What remains is NOT a missing bias-source lemma. The weighted fifth-order
sum L5 and chronological energy still lack the h-dependent estimates
needed for an index/ONE-witness selector. In particular(1)--(2) do not
supply a bound on V_h or dist(nu,Z). Full AG-Pair and original total G3
remain open mathematical claims. No original count/shape/caller requirement
is weakened, and no new homogeneity or coin promise is introduced.

Evidence is this author HAND proof/self-review with OLD accepted providers.
No numerical/symbolic source evaluation, old producer replay, proof-assistant
build, native/QE/model action, local Git change or new worker occurred.
The one active original frontier is the remaining FULL-forest source/
chronology/phase implication, not another quotient-only energy project.

## Appendix: the source coordinate cannot itself bound L5 positively

This is a completed HAND calculation at the SAME fixed7-root source,
not another higher-cap producer. It prevents an invalid strengthening of
(9) to Psi7>=c*v*a^5 on all small equal-arm cells. No source tuple or
coefficient program is evaluated.

Write r_j=g^j+(1-g)^j. For a three-merger history let Lambda_j be its
actual colored holding rate after j events. The quartic coefficient of
its probability is -E[1_event*sum_(j=0)^3 Lambda_j]/24. Summing every
history in the three specified partitions gives

    H32 =66*r2*r3+114*r5+144*r2*r4+108*r3^2+36*r2^2*r3,
    H222=36*r2^3+168*r2*r4+108*r2^2*r3,
    H4  =180*r4+540*r5+216*r2*r4.

For example the3+2 histories have internal holding sum66. For each
ordered placement of its triple/cherry events the cross-block holding
rate is sum_(l<m) k_l*k_m*1_(colors equal). The triple/cherry block-pair
coefficients sum114; the triple/singleton pairs sum144, the cherry/
singleton pairs108, and the singleton pair36. The other two rows follow
from the same current-root counts, with6 or18 histories as displayed in
Section4. These account for every within-block and between-block pair.

Equation(5) therefore gives the EXACT coefficient

    [a^4]Psi7=-(6*H32-6*H222-H4)/(18*24)
             =-v*beta*(17-58v)/12
             =-v*beta*(5+29beta)/24.                 (17)

This agrees with the independent fair-quartic cancellation above.

For clarity the needed fair fifth coefficient can also be counted in
the same small carrier. For a four-entry vector z define

    H2(z)=sum_j z_j^2+sum_(j<k) z_j*z_k.

A three-merger path contributes at degree5 H2(Lambda)/120.
At the fair coin the final-block colors are independent fair. Put
m_j=E[Lambda_j]=(lambda_(7-j)+sum_l lambda_(k_l(j)))/2.
For each distinct pair of eventual blocks let c_lm(j)=k_l(j)*k_m(j).
Different unordered color-pair indicators have zero covariance, even
when they share a block. Their own variance is1/4. Hence exactly

    E[H2(Lambda)]=H2(m)+(1/4)*sum_(l<m)H2(c_lm).       (18)

The three placements of the triple/cherry events are denoted AAB,ABA,BAA.
Each has three internal triple histories. The two other rows represent
six and eighteen histories, respectively. Direct substitution of the
current counts into(18) gives this complete table:

| Path type | 4*H2(m) | sum_(l<m)H2(c_lm) | 4*E[H2(Lambda)] |
| --- | ---: | ---: | ---: |
| 3+2:AAB | 2276 | 249 | 2525 |
| 3+2:ABA | 2276 | 251 | 2527 |
| 3+2:BAA | 2353 | 243 | 2596 |
| 2+2+2 | 2193 | 245 | 2438 |
| 4 | 2527 | 225 | 2752 |

For instance AAB has current group counts
(3,2,1,1),(2,2,1,1),(1,2,1,1),(1,1,1,1).
The other triple/cherry placements just move that one cherry event.
The three-cherry path lowers successive2's to1, and the four-block
path lowers4 to3 to2 to1. Thus the table needs no additional source
evaluation or forest-shape assumption.

Including the fair monochromatic-event probability1/8, history counts
and(5), the combination is

    [a^5]Psi7(B_fair)
      =[(2525+2527+2596-2*2438-2752)/4]/960
      =5/960=1/192.                                (19)

Because the source coefficients divided by v are symmetric polynomials
in g, their change from the fair value is O(beta). From(6),(17),(19), for
each FIXED z>=0, along the actual strict equal-arm curve beta=z*a,

    Psi7(B)=v*a^5*(8*z^2-10*z+1)/48+O_z(a^6).        (20)

Take z=1/6. Its numerator is -4/9, so Psi7<0 for every sufficiently
small positive a. This is an ACTUAL strict source curve: choose

    q=exp(-a), g=(1-sqrt(a/6))/2.

In epsilon=sqrt(a) it is an analytic strict parameter family near0.
At the fair coin, by(19), Psi7>0 for all sufficiently small a instead.
Continuity of the original polynomial source also gives strict rational
survival/coin banks of each sign; none is exhibited or evaluated here.

Consequently Psi7 has BOTH signs arbitrarily close to the ordinary
identity, even with equal arms. The signed fifth-order source remainder
in(9) is essential. A cellwise positivity or one-coordinate positive-L5
shortcut is REFUTED; it must not become another active search task.
This does not refute a bound using the COMPLETE commutator equations
and the actual return/phase fibre. Equations(1)--(2) stay proved.
