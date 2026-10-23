> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# A three-current-root INDEPENDENT private word needs at most one bigon

21 October 2026. Authored HAND THEOREM for review. Exact finite algebra and
univariate polynomial signs were checked in a Wolfram kernel; this is not
independent mathematical review, Lean checking or an original graph-compiler
run. No historical novelty is asserted. General original G3 remains OPEN.
No sub-agent or local Git mutation.

## 1. Precise receiver and proposed conclusion

Take one fresh, unexposed, natural INDEPENDENT private bridge word in the
inherited original source grammar. There are at most THREE entering current
roots. They may carry arbitrary already formed labelled subtrees. The word
has a positive ordinary leading edge and finitely many strict parallel-arm
bigons with positive ordinary connectors. No private bit is exposed, queried,
reused outside its cell or tied to an unbounded external parameter bank.
Retained original IDs/relations remain in the protected core, not in this
fresh word. Matching a capped forest kernel is an internal sufficient
replacement; no extra forest observation is granted to the experiment.

**Claim.** The entire capped labelled forest kernel through three roots of
EVERY such finite word is realized by one strict natural INDEPENDENT bigon
with a positive ordinary leading edge and a positive ordinary connector.
One physical tuple works for all the capped coordinates and their original
joint uses. This is a single-mode statement. It DOES NOT match an arbitrary
paired COMMON/INDEPENDENT tuple using that same replacement.

The source/type, eligible-slot and grafting receiver is inherited from
[admitted testers, Sections 2--5](https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md)
and the [full-source reduction](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md).
Their legality/protected-menu hypotheses are essential. Existing formal
OriginalSpan/Originated declarations were recovered separately; this note
does not assert a new formal fresh-graph insertion theorem.

## 2. The whole forest kernel, not only two hidden statistics

Write Q for pair no-merger probability and R for triple no-merger probability.
Exchangeability and sampling consistency force the following seven-state
kernel on three distinct opaque entering roots. Order the forests as the
three singletons, the three possible pair-plus-singleton forests, and the
three completed rooted binary topologies. The first row is

    [ R, (Q-R)/2, (Q-R)/2, (Q-R)/2,
         (2-3Q+R)/6, (2-3Q+R)/6, (2-3Q+R)/6 ].

Each pair-forest row stays there with probability Q and goes to its unique
completed topology with probability 1-Q. Completed trees stay fixed. Denote
this matrix by M(Q,R). Its empty and one-root kernels are the identity;
the two-root kernel uses Q. Thus these two coordinates determine EVERY
forest coordinate through three entering roots, including grafted subtrees.

For example, sampling a pair from a three-root forest gives
Q=R+(2/3)P(two components), so each pair-forest probability is (Q-R)/2.
Exchangeability makes the three completed topologies equiprobable. Existing
subtrees are opaque roots and are restored by the accepted grafting law.

Direct multiplication, valid as a polynomial identity, gives

    M(Q1,R1) M(Q2,R2) = M(Q1*Q2,R1*R2).                 (1)

The 7-by-7 identity was actually checked symbolically. This is the reason
componentwise multiplication here preserves the whole capped kernel. It
would be false to infer such sufficiency at an arbitrary higher cap.

## 3. A bare INDEPENDENT bigon's exact two-coordinate image

Let p be the probability of choosing the arm with survival x, with the other
arm survival y; 0<p,x,y<1. The ORIGINAL arm labels must be used consistently
when this convention is translated into a parent registry. Routing gives

    Q = p^2*x + (1-p)^2*y + 2p(1-p),
    R = p^3*x^3 + (1-p)^3*y^3
                        + 3p^2(1-p)x + 3p(1-p)^2 y.   (2)

Define U(Q)=3Q-2+2(1-Q)^(3/2), for 0<Q<1. Define L(Q)=0 if
0<Q<=1/2. For 1/2<Q<1, define L parametrically by

    D(v)=2+3v-2v^2-2v^3,
    P(v)=3+6v-2v^2-8v^3,
    Q(v)=2(1-v^2)(1+2v)^2 / D(v)^2,
    L(Q(v))=2v(1+v)^2 P(v) / D(v)^3,
    0<v<1/sqrt(2).                                    (3)

The map Q(v) is strictly increasing from 1/2 to 1, so this is unambiguous.
The bare strict bigon image is exactly the open set

    S = {(Q,R): 0<Q<1, L(Q)<R<U(Q)}.                   (4)

Here is a proof of the nontrivial lower boundary, rather than an inference
from numerical optimization.

Put c=1-Q, a=1-x, b=1-y, h=1-p, u=p*a and w=h*b. The probability d of
one completed three-root component is

    c=p*u+h*w,
    d=[u^2(3p-u)+w^2(3h-w)]/2,
    R=1-3c+2d.                                        (5)

Optimize on the compact closed parameter cube first. At an interior extremum
with c fixed, Lagrange multiplication gives, if u!=w,

    lambda=(3/2)(u+w), p(u-w)=u^2, -h(u-w)=w^2,

which is impossible. If u=w=c>0, the equations force p=h=1/2. On the
fixed-c surface, use p=1/2+e, u=c+h*z, w=c-p*z. The Hessian of d at
(e,z)=(0,0) has determinant -9c^4<0. Thus the only possible interior
critical point is a saddle, and no minimum is lost by checking the boundary.

If p=0 or 1, the result is ordinary, R=Q^3. If one arm has no mergers,
let m be the mass choosing the other arm. Then sqrt(c)<=m<=1 and

    d=(3c^2/m-c^3/m^3)/2.

Its derivative is 3c^2(c-m^2)/(2m^4)<=0. Consequently this boundary has
R>=Q^3. For c<1/2, the remaining boundary has, up to arm symmetry, x=0.
Write s=y, t=p/(1-p). Then

    Q=(s+2t)/(1+t)^2, R=(s^3+3ts)/(1+t)^3.             (6)

At fixed Q, stationarity is

    F(s,t)=2t^2-2(1-s^2)t+s(1-s)^2=0,
    t_+(s)=(1-s)(1+s+sqrt(1+s^2))/2,
    t_-(s)=(1-s)(1+s-sqrt(1+s^2))/2.                  (7)

For t_+, substitute s=2v(v+1)/(2v+1) and
t=(v+1)(1-2v^2)/(2v+1), with 0<v<1/sqrt(2). This gives (3).
For t_-, the SAME rational parametrization uses -1<v<-1/sqrt(2).
Both branches have s strictly increasing, and Q strictly increasing on
their intervals. The plus branch runs Q from 1/2 to 1; the minus branch
runs Q from 0 to 1.

To distinguish their values from the ordinary boundary, let

    sigma(v)=d log R(v)/d log Q(v).

Exact differentiation gives

    sigma(v)-3 = 3(1-2v^2)^2/[v*P(v)].                (8)

P(v)>0 on both intervals, and both branches end at Q=R=1. Hence the
plus branch has R<Q^3, whereas the minus branch has R>Q^3. All other
boundary candidates have R>=Q^3. The unique plus-branch value at a given
1/2<Q<1 is therefore the global minimum L(Q). For Q<=1/2 the closed
minimum is zero, attained when both arms fully coalesce and 2p(1-p)=Q.

For the upper boundary, (5) and

    k(a)=a^2(3-a)/2 <= a^(3/2),  0<=a<=1,

give d<=c^(3/2). Indeed each arm contributes p^3*k(a), bounded by
(p^2*a)^(3/2), and the sum of positive 3/2 powers is at most the 3/2
power of the sum. The bound is attained on the closed cube by x=0,y=1,
p=sqrt(c), giving U(Q); strict natural arms make it strict.

For completeness, strict fibers of (2) have no missing R values. At fixed
Q the allowed p satisfy 2p(1-p)<Q. For Q>1/2 this is one interval;
otherwise there are two intervals exchanged by arm symmetry. For each p,
the (a,b) fiber is a convex open line segment and has the continuous
section a=b=c/[p^2+(1-p)^2]. Thus each component is connected and the two
components have the same R image. Both endpoint values just computed are
approached by strict points keeping Q fixed. Neither endpoint is attained
at strict parameters (the only interior stationary point is a saddle).
The image is consequently the entire open interval in (4).

## 4. The boundary is preserved under serial composition

The exact derivative signs on (3) are crucial. Set

    A(v)=1+2v+2v^2-4v^4-4v^5,
    T(v)=3+12v+12v^2-8v^3-4v^4.

For 0<v<1/sqrt(2), D,P,A,T are positive. Direct differentiation gives

    Q'(v)=4(1+2v) A(v)/D(v)^3 >0,
    sigma'(v)=-3(1-2v^2) T(v)/[v^2 P(v)^2] <0.        (9)

These signs also have elementary bounds: D>=1+2v, P>=2+2v,
A>=1+v, and T>=3+12v on that interval. For the minus branch write v=-z,
1/sqrt(2)<z<1. D(-z)<0, P(-z)>0 and A(-z)>0. For example,
A(-z)>= (2z-1)(2z^2-1)>0. The positivity of P(-z) follows by expanding
3-6z-2z^2+8z^3 about z=1/sqrt(2): its constant, linear, quadratic
and cubic coefficients are respectively 2-sqrt(2), 6-2sqrt(2),
12sqrt(2)-2 and 8. These facts justify the monotonicity used in Section 3.
Both interval sign groups were also checked by exact univariate Resolve.

Let f(c)=-log L(exp(-c)) for 0<=c<log 2, with f(0)=0. Equation (9)
makes f convex: f'=sigma and f''=-Q*d sigma/dQ>0. Convexity and f(0)=0
give f(c1+c2)>=f(c1)+f(c2) whenever c1+c2<log 2. Therefore

    L(Q1*Q2) <= L(Q1)*L(Q2).                           (10)

If Q1*Q2<=1/2 its left side is zero, so (10) still holds.

For U, put z=sqrt(1-Q). Then U=(1-z)^2(1+2z), and

    d log U/d log Q = 3(1+z)/(1+2z).

This slope increases with Q. Thus -log U(exp(-c)) is concave with value
zero at c=0, and

    U(Q1*Q2) >= U(Q1)*U(Q2).                           (11)

Equations (10)--(11) show that S is closed under componentwise products.
Also L(Q)<Q^3<U(Q), so every positive ordinary-edge kernel belongs to S.

## 5. Restore the positive bookends and actual source word

A positive ordinary passage of survival A acts by (Q,R)->(A*Q,A^3*R).
It lies in S, so (10)--(11) put every finite legal word into S. Conversely,
given any (Q,R) in S, openness permits A<1 sufficiently close to 1 that
(Q/A,R/A^3) is still in S. It is the kernel of a strict bare bigon by
Section 3. Give its leading and following ordinary passages survival
sqrt(A), each strictly between zero and one. The resulting legal one-bigon
word realizes (Q,R), hence by Section 2 its COMPLETE cap-three kernel.

For algebraic data, fixed-shape RCF can find algebraic survivals and
inheritance directly. The analytic boundary parametrization is a proof of
completeness, not an extra logarithmic equality oracle in the solver. One
can simply ask the one-bigon RCF formula; failure is NO for this exact capped
private-word interface because the compression proof covers every length.

## 6. Consequence for the original protected template receiver

If a declared single-mode INDEPENDENT original input has a proved entering
cap <=3 at EVERY fresh private bridge slot, replace each word as above.
Keep the original protected core, static tuple, controls, register and all
other rows. Complete kernel equality and accepted eligible-slot insertion
give one actual shared realizing source with at most one extra bigon per
slot. Thus its original all-core recognition reduces to the finite template
and one-bigon-per-slot RCF systems. This is a conditional application with
the exact cap/freshness/receiver predicates, not an assumption that every
original menu has cap three.

For four taxa with one sampled copy of each taxon in every row, an eligible
cut bridge has at most three entering roots: if its descendant side contained
all taxa, its lower endpoint would be a stable ancestor below the retained
lowest stable root. A current root visiting the bridge must descend from
that side, and mergers cannot increase their count. Under the same finite
protected-ID/control contract this gives the stated cap predicate. The
inherited conservative core bounds R_core<=2n-2+2h and slots<=8n-8+6h
then give at most 10n-10+8h hybrids, or 30+8h at n=4. This corollary still
needs independent source-level review with the exact receiver; no graph
census/backend run or formal completion is reported here.

## 7. An explicit neutral cap-three INDEPENDENT cell

There is also a direct algebraic witness for the ordinary point; it does
not depend on solving the boundary optimization. Given a desired pair
survival Q0 in (0,1), choose b in (max(3/4,Q0),1) and put

    S0=4b-2, Delta=sqrt((2-S0)^3/(6S0)),
    p=1/2, x=(S0+Delta)/2, y=(S0-Delta)/2,
    A=Q0/b.

Here 1<S0<2 and 0<Delta<2-S0, so both arms are strict. At p=1/2,

    64*(B3-B2^3) = (S0-2)^3+6*S0*Delta^2 = 0,
    B2=(S0+2)/4=b.

Leading and following survivals sqrt(A) therefore give Q=Q0 and R=Q0^3:
the WHOLE INDEPENDENT forest kernel through three roots is exactly ordinary.
For example the bare algebraic choice S0=1 gives x,y=(1+-1/sqrt(6))/2,
p=1/2, B2=3/4 and B3=27/64; arbitrary targets use S0>1 as above.

The SAME cell's COMMON pair coordinate is A*S0/2=A*(2b-1), strictly
less than Q0 by A*(1-b). This is a useful concrete reminder that an I-only
replacement does not preserve the paired BOTH tuple. The construction also
does not assert exact fitting inside a prescribed coalescent-clock budget:
matching a topology/forest kernel and preserving a particular clock cost
are different receiver obligations.

## 8. Verification and explicit limitations

Actual returned Wolfram checks: symbolic seven-state composition; the
boundary stationarity identity; direct versus stated logarithmic slope;
the fixed-c Hessian determinant; and exact plus/minus interval polynomial
signs. The initial larger Resolve attempt lost its transport and returned
no verdict; its status is UNVERIFIED, not success or NO. A subsequent
numerical grid initially had an invalid iterator; the corrected grid is
exploratory only and is not used as proof of (10) or the image theorem.
No approximate positive gap is used as an exact exclusion certificate.

A tempting balanced-arm lower boundary was rejected by an exact strict
counterexample: p=3/10, x=193/300, y=603/700, and ordinary bookend product
A=9999/10000. Its actual triple probability is LESS than
Q^3-(1-Q)^3. The correct lower boundary is (3), not that balanced formula.

This theorem covers fresh unexposed INDEPENDENT words with at most three
CURRENT entering roots, not merely three total observed leaves. It supplies
no arbitrary higher-cap compression, paired BOTH replacement, exposed-bit
replacement, calendar observation theorem, protected fresh-parameter tie,
general all-input H or complete unrestricted NO algorithm. The original G3
goal remains active and open. The current hand proof and exact finite
computations require separate independent review/formalization before they
are labelled accepted project results.
