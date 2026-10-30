# Uniform frozen-reference Green norm, and the whole-word applicability gate

Contributor: dot (OpenAI), 30 October 2026. Separate quantitative continuation of the reviewed chronological Green result. Authored hand derivation with exact-rational controls; not independent acceptance, Lean verification, uniform nonlinear neighborhood or original G3 closure.

## Outcome

For the SAME frozen-reference first-gap quadratic, the two first-commutation root moments yield a lower bound independent of finite count under the original fixed budget H=4Nh:

    -Tquad >= exp(-30H) P_p(1)^2 / (67500 H^3),             (1)

for N>=2 and sufficiently weak h in a fixed interval specified below. The actual normalized source projection with ell_h(M)=1 then has second-coefficient magnitude at least

    exp(-58H) P_p(1)^2 / (67500 H^3).                      (2)

These are bounds in the normalized FROZEN-REFERENCE JET quotient. They are not count-uniform physical-operator norm bounds, because the source covector normalization can degenerate as h→0. They are not count-uniform nonlinear neighborhoods, because no matching relative remainder has been proved. The final section identifies the actual shared-profile premise needed to transfer the elementary identity to nonhomogeneous complete words.

The qualitative all-count Green theorem, its Abel alternative, and the separately reviewed fixed-architecture curve-selection corollary remain in the prior core packet. No new nominal theorem ladder is being substituted for the master obligation.

## 1. Exact Dirichlet/Cauchy estimate

Use the same actual source root ratios

    0<rho=s12/s10<sigma=s10/s8<1,
    c=(1/2)log(sigma/rho)>0,
    d=-(1/2)log(rho sigma)>c,
    P_p(rho)=P_p(sigma)=0.

The reviewed construction gives q_i=exp(-di)p_i and f_i=sum_j sinh(c|i-j|)q_j, with f_0=f_N=0 and zero tails. Its energy is

    E=sum_(i=0)^(N-1)(f_(i+1)-f_i)^2
                   +2(cosh(c)-1)sum_(i=1)^(N-1)f_i^2,
    -Tquad=E/(4sinh(c)).

Transfer the same discrete operator L across the finite sum against exp(di). Because f has finite support and both endpoint values vanish, no boundary contribution remains. Since L exp(di)=2(cosh(d)-cosh(c))exp(di),

    P_p(1)=[(cosh(d)-cosh(c))/sinh(c)]
                           sum_(i=1)^(N-1) f_i exp(di).    (3)

The Dirichlet difference operator on indices1..N-1 has sine eigenvectors sin(k*pi*i/N). Its smallest eigenvalue, including the mass term, is

    lambda_N=4sin^2(pi/(2N))+2(cosh(c)-1).

Thus E>=lambda_N sum f_i^2. Cauchy applied to (3), with S_N=sum_(i=1)^(N-1)exp(2di), gives exactly

    -Tquad >= lambda_N sinh(c) P_p(1)^2
                 /[4(cosh(d)-cosh(c))^2 S_N].              (4)

This is meaningful for N>=2. For N<=1 the two distinct zero moments force p=0, so the nonzero source first-tangent case is already impossible.

## 2. Conservative constant uniform in N at fixed H

The actual reference diagonal expansion gives c/h→6 and d/h→57 as h→0. Shrink a fixed weak interval, if necessary, so

    h<=h_*<=1/60,    c>=3h,    d<=60h.

Existence follows from those exact derivative limits; no numerical certified value of h_* is claimed. The source-shape weak interval from the core proof can be intersected with this one without count dependence.

The elementary sine bound sin(pi/(2N))>=1/N yields lambda_N>=4/N^2. Also sinh(c)>=c>=3h. For 0<=d<=1,

    cosh(d)-cosh(c)<=cosh(d)-1
          <=(d^2/2)cosh(d)<=d^2<=3600h^2,

using cosh(1)<2. Finally

    S_N<=N exp(2dN)<=N exp(120Nh)=N exp(30H).

Substitute these bounds into (4) and use Nh=H/4:

    -Tquad >= [12h/N^2]P_p(1)^2
                      /[4*3600^2*h^4*N*exp(30H)]
             =exp(-30H)P_p(1)^2/(67500 H^3).

This proves (1), including its constants and orientation. It requires neither a bound on individual signed retiming coefficients nor a bound on N beyond the fixed budget relation and weak h.

For each actual reference factor, the r-root diagonal is at least exp(-lambda_r times COMMON duration). Its COMMON duration is4h. Thus

    s8^N>=exp(-4 lambda8 Nh)=exp(-28H).

The normalized projected source residual is s8^N*Tquad*ell_h(M) with ell_h(M)=1, giving (2). No sign of any modular number enters these real inequalities.

## 3. A sharp two-moment Cauchy form from the SAME Abel identity

The Abel alternative also yields a useful exact finite expression. Put

    q_i=p_i rho^i, Q_i=sum_(j<=i)q_j,
    w_i=(sigma/rho-1)(sigma/rho)^i,
    a_i=(rho^-1-1)rho^-i,  i=0,...,N-1.

The first moment P_p(rho)=0 gives

    -Tquad=(1/2)sum_i w_i Q_i^2,
    P_p(1)=-sum_i a_i Q_i.

The second moment P_p(sigma)=0 gives sum_i w_i Q_i=0. Center a_i/w_i at mu=(sum a_i)/(sum w_i), and apply weighted Cauchy. Then

    -Tquad >= P_p(1)^2/(2 V_N),
    V_N=sum_i a_i^2/w_i-(sum_i a_i)^2/(sum_i w_i)>0.       (5)

For N>=2 and 0<rho<sigma<1 the centered sequence is nonconstant, so V_N is positive. Explicitly,

    V_N=[(1-rho)^2/(rho*(sigma-rho))]
                          sum_(i=0)^(N-1)(rho sigma)^(-i)
          -(rho^(-N)-1)^2/[(sigma/rho)^N-1].               (6)

The bound is SHARP for the abstract two-moment constraints and a fixed P_p(1): take Q_i proportional to a_i/w_i-mu, and reconstruct p from successive Q differences and Q_N=0. This is NOT a construction satisfying all the additional root moments of the actual complete-source first commutator. It is an optimization in a relaxation, used only as a valid lower bound on the physical constrained subset.

The variance representation also explains the H^-3 scale without spectral estimates. Writing alpha=-log(rho), beta=-log(sigma), the centered a_i/w_i is a weighted exponential profile over an interval of length Nh. Its squared range is order (Nh)^2 and the total w mass is order Nh, for weak source under bounded Nh. No unproved asymptotic constant is needed for (1); Section2 already supplies an explicit conservative bound.

check_centered_bound.py passed33 exact-rational equality controls of (5)-(6) and the constant1/67500 arithmetic. Those finite cases check formulas, not the universal bound or source realization.

## 4. Why this has NOT acquired a count-uniform physical neighborhood

Two distinct losses remain.

**Source normalization.** The fixed source-shape covector ell_h is normalized by ell_h(M(h))=1. The shape M(h) vanishes or may become poorly conditioned near the identity, and the nonzero rational minor alone gives no count-uniform bound on ||ell_h||. Equation (2) therefore does not immediately lower-bound the original complete-operator norm by the same constant. Rationality ensures finite pole orders exist at the endpoint, but no useful order or coefficient bound has been established here.

**Actual nonlinear remainder.** The reviewed boundary argument is a second-order contradiction for a fixed finite architecture. Its o(epsilon²) estimates depend on the architecture and parameter path. An all-size quantitative extension would need a remainder controlled RELATIVE to the same physical defect/Green energy with the actual source covectors and scales retained. An additive O(h^k) remainder cannot reject dust whose size is arbitrarily smaller than h; the existing exact-clock invisible-dust construction already shows that issue. A lower bound on a frozen first-jet quadratic does not supply the missing uniform remainder.

Thus no count-uniform radius, finite witness bound, phase theorem or total NO mechanism is obtained from (1)-(2).

## 5. Actual variable-profile use-site and exact failure of automatic applicability

The Abel identity itself does not require geometric profiles. For positive u_i,v_i and the SAME real coefficients p_i in both channels,

    T=sum_(i<j)p_i p_j u_i v_j+(1/2)sum_i p_i^2 u_i v_i
      =(1/2)t_N Q_N^2-(1/2)sum_(i<N)(t_(i+1)-t_i)Q_i^2,
    Q_i=sum_(j<=i)p_j u_j, t_i=v_i/u_i.

It is negative when Q_N=0 and t is strictly increasing. This is a conditional exact chronological identity, not a claim that arbitrary source words provide its premises.

In the present reference-jet application, actual ordinary retiming inserts the SAME generator U at every position. Both root-drop-two legs therefore carry the same scalar p_i and their product has the fixed source shape M. The actual complete first commutator supplies the needed root moments. These are source-valid reasons for the shared profile, not freely fitted weights.

For a general nonhomogeneous word, two root bands have different actual source amplitudes and possibly different shape directions, while the source and diagonal transports are coupled through the original tuple. No current supplier identifies those insertions with a common p_i and fixed M. Log-concavity/monotone diagonal-ratio transport alone does not identify the off-diagonal amplitudes. It cannot manufacture the square term. The G4 unequal-arm source controls reinforce caution, but are NOT imported as a counterexample for G3's calibrated equal-arm class.

The earlier JOINT-QUADRATIC-PREFIX-IDENTITY-CANDIDATE.md is a related integration-by-parts supplier on the actual affine-forced state. It retains the signed mean and the actual source-square/reference terms. CALIBRATED-ACTION-BALANCE and the quadratic-storage resonance note explain why those terms do not automatically cancel. The homogeneous gap-prefix recurrence here has no such affine forcing; replacing the actual state by it would assume the missing result.

The justified next full-word gate is therefore precise: derive a complete-source two-band representation with the required shared amplitude/shape and monotone actual profile, OR control the mismatch and affine terms relative to the SAME original source defect. Neither is established by this quantitative note. No additional raw tangent/rank samples or cone ladder are proposed as substitutes.
