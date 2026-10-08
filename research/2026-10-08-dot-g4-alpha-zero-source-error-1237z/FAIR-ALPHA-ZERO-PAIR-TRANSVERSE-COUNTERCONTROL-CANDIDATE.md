# The fair pair-normalized transverse error survives on alpha=0

Contributor: dot (OpenAI), 8 October 2026, 12:27 UTC.

Status: HAND CANDIDATE FOR INDEPENDENT REVIEW. A bounded source-relative error test for the separately owned multiscale energy estimate. No compiler, numerical or symbolic source execution, parameter scan, finite-cap bank extension, or publication was used. All earlier frozen source proofs are unchanged.

## 1. Actual source and precise answer

Use fixed fair INDEPENDENT routing and the actual bare-cell chart

    x=2h epsilon^2-4u epsilon^3,
    y=2h epsilon^2+4u epsilon^3,
    g=1/2,
    h>0, u^2=h^3/12.                                    (1)

The omitted common-chart parameters are w=v=0. In particular alpha=h^3-12u^2 is exactly zero. For every fixed h>0 and either allowed sign of u, both arm durations are strictly positive for sufficiently small positive epsilon. The same actual tuple is used at every arity.

Put mu=h epsilon^2, delta=(x-y)/2=-4u epsilon^3. Then

    x=2mu+delta, y=2mu-delta, delta^2=(4/3)mu^3.

Let t_pair=-log b2(B) be the cell's TRUE pair hazard, and use the algebraic left normalization C_pair=E_(-t_pair)B. This does not insert a negative physical population.

The candidate result is

    X(C_pair)=Y(C_pair)=(2/15)mu^4+O(mu^5),
    U(C_pair)+(5/3)X(C_pair)=-(4/3)mu^5+O(mu^6),
    T(C_pair)-(5/3)X(C_pair)=(28/15)mu^5+O(mu^6).           (2)

Thus both order-ten-in-epsilon transverse errors are genuinely NONZERO on the leading alpha=0 locus. Since t_pair/mu tends to one, they also have genuinely nonzero order-five true-hazard coefficients. In particular, an estimate forcing these remainders to vanish whenever alpha=0 cannot hold on the actual source.

This supplies one source-valid obstruction to that proposed relative-error shortcut. It does not exhibit a full ordinary word, satisfy the fourth-defect cancellation, prove sharpness of a complete word-level error estimate, or rule out using the fourth-defect equation jointly with the energy identity.

## 2. Source formulas and second ordinary correction

Retain the exact accepted source quantities

    A_n=3p_n(2,2,1^(n-4))-2p_n(3,1^(n-3)),
    f=d9=A9/15, H=d6=A6/9,
    e=[2p7(3,2,1,1)-p7(4,1,1,1)]/6.

The bare representation is X=Y=f, T=H, U=-H+2e, V=0. These probabilities refer to specified partitions under the actual two-arm routing; no independently adjustable matrix entries are substituted.

For an ordinary partition of N roots into R blocks, let d=N-R and lambda_j=j(j-1)/2. The finite holding-time simplex expansion, one order beyond the already accepted first correction, is

    q_(N,R)(t)=t^d/2^d [1-c1 t+c2 t^2+O(t^3)],
    c1=(sum_(j=R)^N lambda_j)/(d+1),
    c2=[(sum lambda_j)^2+sum lambda_j^2]
                           /[2(d+1)(d+2)].               (3)

For example, the second coefficient is the complete homogeneous degree-two polynomial in the d+1 holding rates divided by (d+1)(d+2). The ordered-simplex integral of every squared holding interval and every distinct pair gives (3), including d=0. The probability of one specified partition is product(s_i!) times q.

It is useful to write

    c2=(1/2)c1^2+k(R,d),
    k(R,d)=d/24 [(R+(d-1)/2)^2+(d-1)(d+3)/60].            (4)

To verify (4), use the variance of lambda_(R+J) for J uniform on {0,...,d}. With Z=J-d/2,

    E[Z^2]=d(d+2)/12,
    Var(Z^2)=d(d+2)(d-1)(d+3)/180,

and the linear and quadratic centered parts are orthogonal. Substitution in (3) yields (4). No stochastic limit or source approximation is used in this coefficient identity.

## 3. General fair block-assignment coefficients

For output blocks of sizes s_i, set d_i=s_i-1, d=sum d_i, R=number of blocks, s2=sum d_i^2, and K=product(s_i!)/2^d. After the leading arm factors are extracted, the output blocks are independently assigned to the arms with probability one half. Write their signs as sigma_i in {-1,1}.

The accepted first ordinary rate polynomial on arm A is

    R_A=sum_i a_i I_i+sum_(i<j) b_ij I_i I_j,
    a_i=(d_i^2+2d_i)/6,
    b_ij=1+(d_i+d_j)/2+d_i*d_j/3,
    I_i=(1+sigma_i)/2,

with R_B obtained by complementing the indicators. Denote the balanced first correction by

    C_shape=(1/2)[(R+d)(R-1)+(d^2+4d+s2)/3].

Thus the degree-(d+1) term at delta=0 is -K C_shape mu^(d+1).

### The delta-squared correction

The degree-(d+1) coefficient of mu^(d-1)delta^2 is -K W_shape, where

    W_shape=(s2-d)C_shape/8
          +(1/4)sum_(i<j)d_i*d_j*b_ij
          +(1/2)sum_i d_i*a_i
          +(1/4)sum_(i<j)(d_i+d_j)b_ij.                   (5)

Indeed, putting D=sum d_i sigma_i, the leading duration product expands as

    s^d_A t^(d-d_A)
       =mu^d[1+(delta/(2mu))D
                +(delta^2/(8mu^2))(D^2-d)+...],
    s=mu+delta/2, t=mu-delta/2.

The extra ordinary duration factor is 2mu(R_A+R_B)+delta(R_A-R_B). Also

    R_A+R_B=C_shape/2+(1/2)sum b_ij sigma_i sigma_j,
    R_A-R_B=sum_i[a_i+(1/2)sum_(j!=i)b_ij]sigma_i.

Multiplying and averaging independent fair signs gives exactly (5). In particular this is an actual fair-source imbalance correction, not a free shape parameter.

### The balanced second correction

The degree-(d+2) balanced coefficient is +K J_shape mu^(d+2), where

    J_shape=C_shape^2/2+(1/2)sum_(i<j)b_ij^2+K_shape,

    K_shape=[15dR^2+15dR-18d+(15R+16)d^2+4d^3
                              +(15R+12d-14)s2]/360.       (6)

Here the second-order product of the two ordinary expansions is

    4 E[c2_A+c2_B+R_A R_B]
      =2 E[(R_A+R_B)^2]+4 E[k_A+k_B].

The first expectation gives C_shape^2/2+(1/2)sum b_ij^2. To check the remaining term, for the fair arm block count R_A^count and root drop d_A use

    E[d_A]=d/2,
    E[d_A^2]=(d^2+s2)/4,
    E[d_A^3]=(d^3+3d*s2)/8,
    E[d_A R_A^count]=d(R+1)/4,
    E[d_A (R_A^count)^2]=d(R^2+3R)/8,
    E[d_A^2 R_A^count]=[(R+2)d^2+R*s2]/8.

Expanding (4) and substituting these finite Bernoulli moments proves (6). A count symbol here is distinct from the rate polynomial R_A. Empty arms cause no exception.

## 4. The required actual partition combinations

For d=2 at n=9, direct substitution into (5)-(6) gives

    shape          K       C_shape       W_shape       J_shape
    (2,2)          1        88/3             6          2735/6
    (3)           3/2       89/3            59/4         2801/6.

Together with the exact degree-two difference -3delta^2/4, this yields

    A9=-(3/4)delta^2+mu^3
                    +(105/4)mu*delta^2-33mu^4+O(epsilon^10).  (7)

For d=3 and total root number n, the three relevant shapes have

    W4=3n(n+1)/8,
    W32=(n^2+7n-2)/8,
    W222=(9n-6)/8,

    J4-J32=(5n^2-10n-23)/15,
    J32-J222=(5n^2-10n-8)/30.                              (8)

These follow from (5)-(6) with loss patterns (3), (2,1), (1,1,1), respectively. Their leading K values are 3, 3/2, 1. The previously accepted balanced first corrections are C4=n(n-4)/2+5, C32=n(n-4)/2+13/3, C222=n(n-4)/2+4.

Use the exact selected-label identity

    A_n-A_(n-1)=2(n-7)P32+2P4-3(n-5)P222.

The coefficient of mu^2 delta^2 in its degree-four term is

    -3(n-7)W32-6W4+3(n-5)W222
      =[-3n^3+9n^2-18n+48]/8.

Its degree-five balanced coefficient is

    6(J4-J32)+3(n-5)(J32-J222)
      =[5n^3-15n^2+2n-52]/10.

For n=7,8,9 these respective coefficient lists are

    -333/4, -132, -393/2;
    471/5, 782/5, 1198/5.

Their sums are -1647/4 and 2451/5. Including the accepted lower-degree terms therefore gives

    A9-A6=(63/4)mu*delta^2-21mu^4
                  -(1647/4)mu^2*delta^2+(2451/5)mu^5
                  +O(epsilon^12).                        (9)

For e at n=7, the degree-four delta-squared coefficient is
(W4-W32)/2=(21-12)/2=9/2, while the degree-five balanced coefficient is
(J32-J4)/2=-76/15. Consequently

    e=-(1/4)mu*delta^2+mu^4/3
                  +(9/2)mu^2*delta^2-(76/15)mu^5
                  +O(epsilon^12).                        (10)

Fair arm exchange makes every expression even in delta and even in epsilon. The unretained degree-four delta^4 terms start at epsilon^12, degree-five delta^2 terms also start there, and degree-six balanced terms start there. This justifies the remainders in (9)-(10); no degree-ten term is omitted.

## 5. Restriction to alpha=0 and normalization

On (1), delta^2=(4/3)mu^3 exactly. Equations (7)-(10) simplify to

    A9=2mu^4+O(mu^5),
    A9-A6=-(294/5)mu^5+O(mu^6),
    e=(14/15)mu^5+O(mu^6).                               (11)

Thus f=(2/15)mu^4+O(mu^5), and the bare transverse combinations are

    U(B)+(5/3)f=(A9-A6)/9+2e
                    =-(14/3)mu^5+O(mu^6),
    H-(5/3)f=-(A9-A6)/9=(98/15)mu^5+O(mu^6).             (12)

First use nominal left normalization C_nom=E_(-mu)B. The exact row scalings are exp(36mu) for X=Y, exp(21mu) for U, and exp(15mu) for T. At order mu^5, their additional transverse contributions are +25mu*f and -35mu*f. Using (11), these are +(10/3)mu^5 and -(14/3)mu^5. Substituting into (12) yields

    U(C_nom)+(5/3)X(C_nom)=-(4/3)mu^5+O(mu^6),
    T(C_nom)-(5/3)X(C_nom)=(28/15)mu^5+O(mu^6).            (13)

The true pair survival is exactly

    b2(B)=1/2+(1/2)exp(-2mu)cosh(delta).

It follows that t_pair=mu+O(mu^2), and t_pair>0 for this strict source. Replacing nominal by pair left normalization changes the time by Delta=O(mu^2). The exact difference in the first transverse combination is

    (exp(21Delta)-1)L_nom
      +(5/3)(exp(36Delta)-exp(21Delta))X(C_nom).

Here L_nom=O(mu^5), X(C_nom)=O(mu^4), so this difference is O(mu^6). The analogous T expression has the same bound. Hence (13) proves the pair-normalized result (2), including its genuinely nonzero leading constants.

## 6. Consequence for the source-relative error question

The accepted general fair estimate places these mismatches at O(epsilon^10)=O(t_pair^5). This candidate shows that their leading order-five constants do not carry a factor alpha. Their vanishing on alpha=0 is therefore unavailable as a mechanism for reducing a multiscale cross-error estimate. In particular the stronger hypothetical bound by a constant times alpha^2*t_pair^5, or any other expression vanishing identically at alpha=0, fails on this actual family.

The source is nonetheless not a complete ordinary endpoint. Its leading fourth log-Newton defect remains J4=-h^4 on alpha=0. Thus this countercontrol does not satisfy word-level fourth-defect cancellation, does not establish a multiscale full-return construction, and does not decide whether energy plus that diagonal constraint gives a stronger joint estimate. The parallel hazard argument retains that remaining obligation.

## 7. Prior formulas, pins and verification boundary

The unchanged six-provider ledger is `SOURCE-PINS.json`, SHA-256 `7b3a314baa17670e30f4c78b129493577e6873728c3ea6c0f1899d30d440070a`. The accepted fair source proof is frozen SHA-256 `88a1509eed7af6f28ee1be7478462e44937e093c17038dac78f784ef1ed283aa`, with independent review `f459e2e3814f24a9d228fe94ca92c6f9742d257f28d8d51345afa55d40aa3fea`. Its public editorial derivative at commit `df871563c361f8a225f9631984a0e35caa381d1c` has proof hash `92e8d834104ecc1127140836e90699c75e28440bc913a981749baf98bb4e955c`; the original/public mapping is preserved there.

The previously accepted rank-two fair argument uses a multi-cell c*f cross term in the full nominal chart. That term disappears under pair normalization and does not determine (2). The source-only interior addendum and the separately accepted biased order-nine calculation likewise do not evaluate this fair order-ten coefficient. This note supplies the missing single-cell calculation without modifying those results.

Before this derivation was frozen, the existing Codex exact chronological-energy note and its mandatory jet-grade correction were recovered at commit `34a36b3096e650e05a8f258c0e4d480511e4056f`:

- `research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-stopping/two-insertion/EXACT-CHRONOLOGICAL-ENERGY-DEFECT.md`, Git blob `2ab2880d17a976cf8d5505e83ef4bd51c5e3fe01`.
- The same directory's `JET-DEFECT-IDENTITY-AND-CORRECTION.md`, Git blob `dd976e8427773cb76e3a8d2db8ab4f866d564243`.

Those sources supply exact arbitrary-word defects and a separate rare-route quartic calculation with g tending to zero; they are retained as prior controls, not treated as a fixed-fair parabolic alpha-zero formula. No historical novelty conclusion is drawn from this scoped source check.

The new work here is a hand holding-time/finite-Bernoulli coefficient derivation and its actual-source specialization. It is not an energy theorem, a new bank, a full ordinary return, an all-length no-return theorem, a cap-uniform hazard result, or original G4 closure.
