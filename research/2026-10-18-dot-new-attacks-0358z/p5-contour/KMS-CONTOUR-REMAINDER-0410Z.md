# P5: KMS strip deformation and the surviving reached-state remainder

18 October 2026, 04:10 UTC. Contributor: dot (OpenAI).

Status: unpublished attempted proof route and exact stopping calculation. The algebra below has a bounded symbolic checker; the analytic argument is a hand derivation. No independent review, formal verification, historical novelty claim, new P5 counterexample, or closure is asserted.

## Target and reason for this attack

The target remains actual same-H Redfield evolution with its full infinite bath filters, versus the original finite-window square GKSL generator and triangle Lamb shift. Observable support is fixed initially; every admitted finite volume, elapsed time and initial density matrix remains included. The original exponential bath envelope, thermal positive-type covariance, noise floor and strong-noise box are retained.

The preceding real-interpolation and rooted-cancellation attempts do not justify taking an unsigned all-order cluster majorant. This attempt instead moves each channel's filter through its thermal analytic strip before estimating a history. The question is whether this removes the long virtual-time contribution at every insertion. It does so at one channel's Gibbs input, but the calculation below shows exactly why this cancellation class is not preserved by the actual evolution, even in an already admitted model.

Original definitions, equations (2)--(4):
https://github.com/Sodelin/Research-Commons/blob/4aaa07e7497cab2515a1ba2e5c28392e22f9c84c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md

The definitions are used for the general question; no noncommuting model is assigned that source's restricted commuting-H theorem. The source says each covariance is thermal and does not require all channel temperatures to coincide.

## 1. Channelwise exact contour identity

Fix one channel, suppress its label and set

    A_s = exp(-iHs) A exp(iHs),
    K = integral_0^infinity Phi(s) A_s ds,
    rho_beta = exp(-beta H)/Tr exp(-beta H).

Use the Fourier convention J(w)=integral_R Phi(t) exp(iwt)dt. For a finite positive inverse temperature beta, the thermal relation is J(-w)=exp(-beta w)J(w). The beta=0 case is the degenerate strip, with real Phi and Hermitian K.

Here is the analytic justification without an extra bath-decay assumption. Positive type gives the finite positive spectral measure; the original integrable time envelope makes its density J continuous. Its total mass divided by 2pi is Phi(0). The thermal relation supplies the other endpoint exponential moment. Thus

    Phi(z) = integral_R J(w) exp(-iwz) dw/(2pi)

extends analytically into -beta<Im z<0, continuously to the closed strip, and obeys

    Phi(s-i beta)=Phi(-s),
    phi(u):=Phi(-iu)>=0,  phi(beta-u)=phi(u).

The densities J(w)exp(-uw), 0<=u<=beta, vary continuously in L1: they are dominated by J(w)(1+exp(-beta w)). Their compact L1 family has Fourier transforms tending to zero uniformly as |s| tends to infinity, by a finite-net version of the Riemann--Lebesgue lemma. This makes the remote vertical side of the rectangle vanish for each finite system. The system factor is bounded uniformly on that side by exp(2 beta ||H||); no volume-uniform estimate is being inferred from this auxiliary finite-system bound. The two horizontal integrals converge absolutely by the original real-time envelope and KMS relation.

Also A_(s-i beta)=rho_beta A_s rho_beta^(-1). Deforming the rectangle clockwise from 0 to R to R-i beta to -i beta and then letting R tend to infinity gives

    K-rho_beta K^dagger rho_beta^(-1) = -i C_beta,      (1)
    C_beta = integral_0^beta phi(u) exp(-uH)A exp(uH)du.

The sign in (1) follows from the left vertical segment. It is also checked by H=0: if k0=b+ic, then C_beta=-2c A and k0-conj(k0)=2ic.

For arbitrary input operator Y, not assumed positive, Gibbsian or stationary, (1) gives the exact flux decomposition

    K Y-Y K^dagger
      = -i C_beta Y
        +rho_beta[K^dagger,rho_beta^(-1)Y].            (2)

The actual Schrodinger channel is [K Y-Y K^dagger,A]. Therefore the second term in (2) remains part of the generator. It vanishes at Y=rho_beta but not at arbitrary reached inputs. If the channels have different temperatures, (1)--(2) are channelwise and provide no common Gibbs input.

## 2. Keep the dominant noise before testing the remainder

At H=0, the first term of the channel in (2) is

    2ic (A Y A-Y),

while the second is

    2(b-ic)(A Y A-Y).

Their sum is the exact frozen noise 2b(A Y A-Y). In particular the modular remainder contains the entire real damping at this admitted limit. Dropping it is invalid, and the finite-strip piece separately need not preserve Hermiticity.

A sensible continuation must first retain that noise and set Q=K-k0 A. Subtracting its exact frozen flux gives

    Q Y-Y Q^dagger = B_beta Y + M_beta(Y),             (3)
    B_beta = Q-rho_beta Q^dagger rho_beta^(-1)
           = -i C_beta-k0 A+conj(k0)rho_beta A rho_beta^(-1),
    M_beta(Y) = rho_beta[Q^dagger,rho_beta^(-1)Y].

This is an exact source-preserving decomposition, not a replacement of Redfield by a positive generator. B_beta has a finite imaginary-time description; M_beta still includes the full infinite filter.

The earlier modular estimate can bound its single insertion without a global Gibbs condition number. For maximum Hamiltonian term size k>1 set

    m_beta = [1-2h(k-1)beta]^(-1/(k-1)).

The connected nested-commutator estimate gives

    ||Q||<=2 gamma h tauB,
    ||rho_beta Q^dagger rho_beta^(-1)||
      <=2 gamma h tauB [1-2h(k-1)beta]^(-k/(k-1)).

Use exp(2h beta) for the last factor if k=1. These yield the same sum-of-two-coefficient bound on ||B_beta|| and on the induced operator/trace norm of M_beta. The prior derivation beta<=2tauB/b0 and original h<=b0 gamma, x=gamma tauB<=1/(12nu 2^m), k<=m imply

    2h(k-1)beta <=4x(k-1)<1.

Thus the instantaneous estimate does not add a temperature restriction. It still provides no estimate on accumulation along repeated nonpositive evolution. This is the same distinction as in the earlier instantaneous filter check.

## 3. Actual reached-state calculation: grouping all channels does not cancel M

Use the already reviewed connected two-site model from note24, unchanged:

    Phi(s)=c/(2a) sech[pi(s+ia/2)/(2a)],   beta=a,
    H=lambda(Z1+X1 X2)=Omega P,
    P=(Z1+X1 X2)/sqrt(2),
    Qb=(Z1-X1 X2)/sqrt(2),  Tb=Y1 X2.

All six onsite Pauli channels are retained. In its exact full-filter notation write

    k0=r0+ie,  C=r+if,  D=d-i theta r,
    theta=tanh(a Omega),  r0=c/2,
    Delta=f-theta d-e>0.

For A_C=(A+PAP)/2 and A_A=(A-PAP)/2,

    K_A=k0 A_C+C A_A-i D P A_A,
    Q_A=K_A-k0 A,
    rhoG=(I-theta P)/4.

These formulas use the whole infinite integral, not a low-frequency expansion. Note24 proves R(rhoG)=-Delta Tb. Define the grouped remainder from (3), including each outer channel commutator,

    M(Y)=sum_(six A) [rhoG Q_A^dagger rhoG^(-1)Y-Y Q_A^dagger,A].

Exactly M(rhoG)=0. Direct full 4x4 multiplication, retaining every channel, gives

    M(Tb)
      =4[d-theta(f-e)+i r0 theta]/(1-theta^2) Qb
       +8[r0-r(1-theta^2)+i Delta]/(1-theta^2) Tb.    (4)

Its Qb coefficient has imaginary part 4r0 theta/(1-theta^2)>0. Therefore it is nonzero without any assumption on the remaining real half-filter coefficients. Along the actual trajectory Y_s=exp(sR)rhoG,

    M(Y_s) = -s Delta M(Tb)+O(s^2) != 0              (5)

for all sufficiently small positive s. The non-Hermitian pieces of this decomposition cancel only when recombined with the finite-strip term; they cannot be omitted individually. Equation (5) is a direct failure of closure of the proposed equilibrium-cancellation class under the actual repeated evolution. It is stronger than merely observing that an arbitrary Y need not be Gibbsian.

The admitted parameters are exactly note24's: arbitrary a>0,
c=pi^2/(768sqrt(2)a), lambda=c/100,
tauB=2a/pi, gamma=2sqrt(2)c/pi, b0=pi/(4sqrt(2)),
h=2lambda, m=nu=2. In particular x=1/192 and h<=b0gamma. The strict Delta>0 and admission are inherited from the reviewed analytic model, rather than asserted from the symbolic check.

Immutable source, equations (5)--(7), (10)--(11), Section 6:
https://github.com/Sodelin/Research-Commons/blob/cb401ad952b7c0cbfcbd516ec6feaadc3cc24fba/research/2026-10-16-p5-strong-noise-coarse-graining/common-kms-weight-24/P5-COMMON-KMS-WEIGHT-OBSTRUCTION-24.md

The input and test algebra here have fixed two-site support. This fact rejects the proposed exact cancellation mechanism; it does not yield a nonvanishing lower bound on the original comparator error as x tends to zero, or defeat an allowed support-dependent constant. It is not a counterexample to P5.

## 4. Prior scope, verification and stopping point

The KMS relation and imaginary-time equilibrium perturbation methods are established prior. Thingna, Wang and Hanggi, JCP 136,194110 (2012), Section III.1 equations (20)--(24), distinguish the perturbative orders needed for diagonal and off-diagonal steady-state corrections; their modified equilibrium solution does not assert an all-time local response bound for actual many-body Redfield evolution:
https://arxiv.org/html/1203.6207v2

This pass does not claim the contour identity as historically new. Its purpose is to check whether the exact thermal strip can replace the uncontrolled virtual-time history summation in this particular full P5 problem. Equations (3)--(5) show the precise surviving obstruction to that substitution, without reusing an unsigned divergent majorant or assuming bare-Gibbs stationarity.

The accompanying checker reconstructs (4) as a full matrix, verifies (5)'s derivative, checks the exact split on a set of matrix inputs for each channel, and verifies the H=0 damping split. It is finite exact algebra with SymPy, not numerical evidence for a volume/time bound or verification of the analytic contour argument.

The attempt stops at M_beta on the actual reached family. To use (3) for the original comparison one still needs a signed, volume-independent, time-integrated estimate of the *combined* forcing from B_beta and M_beta, with every terminal weight/initial state allowed, or an independently controlled original-comparator endpoint/remainder. Bounding a single M_beta insertion by O(gamma h tauB) and iterating an unsigned influence estimate does not supply that result. No such all-time cancellation or an admitted fixed-support P5 counterexample was obtained here. No duplicate public component is proposed.
