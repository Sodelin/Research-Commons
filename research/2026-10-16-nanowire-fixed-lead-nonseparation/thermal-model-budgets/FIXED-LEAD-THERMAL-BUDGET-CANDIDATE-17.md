# Exact fixed-lead finite-energy budget for the thermal certificate

17 October 2026 UTC. dot (OpenAI), with Nolan. Candidate for hand review. Classical resolvent/lead-matching application; no novelty, execution, experimental validation or Lean claim.

## Scope and inputs

Use the exact normal leads of the accepted finite-pair packet b6b1f91d84e58506b9028dec1ff0c59e05317224, finite-example/FINITE-PAIR-CERTIFICATE-02.md: zero onsite, lead hopping and contact hopping -tau_z times u, u=1 meV. The finite wire Hamiltonian is Hermitian, energy independent and has the declared physical PHS at zero energy; internal dissipation is zero. No change to wire size, hopping, contact or potential is made. The following argument works at each fixed common field. Uniform field claims require uniform input bounds.

Normalize all energies by u: x=E/u, h=H/u. Let P embed all endpoint channels into the wire, with P*P=I and Pi=PP*. The two contacts are disjoint. N denotes electron channels in the measured left lead, including spin (N=2 for the saved spinful chain).

Required numerical/scientific input is a *certified lower bound* rho>0 on s_min(K(0)), where K(0)=-h+i Pi. Neither an unvalidated floating-point inverse nor the existing determinant interval alone supplies rho. No such numerical rho is claimed here.

## 1. Exact lead and channel conventions

For |x|<2 the retarded surface Green function of either electron or hole semi-infinite chain is s(x)=x/2-i beta(x), beta(x)=sqrt(1-x^2/4). It solves s=1/(x-s), with the retarded branch. Opposite signs of hopping have the same surface Green function; contact signs cancel in the self-energy. Therefore

    K(x)=x I-h-s(x)Pi.

In a flux-normalized channel gauge the scattering matrix is

    S_tilde(x)=I-2i beta(x) P* K(x)^(-1) P.

Lead reference-plane phases can multiply this matrix on the incoming/outgoing sides. Those phases are diagonal in the electron/hole channels and hence preserve the reflection/transmission probabilities and conductance. At zero energy the normalization agrees with the accepted r=I-2iG convention. The derivative below is for this probability-equivalent gauge, not a claim about an arbitrary channel phase convention.

For example, an electron chain with x=-2 cos k and incoming/outgoing waves exp(-ik(n-1)), exp(ik(n-1)) has physical S=-exp(2ik) S_tilde. Direct boundary matching gives this phase. Hole channels are treated with their opposite group-velocity convention and have the corresponding diagonal phases.

K-K*=2i beta Pi. The inverse identity G-G*=-2i beta G Pi G* gives S_tilde S_tilde*=I by expansion. Thus every reflection subblock is contractive throughout this window. This argument does not assert PHS at a nonzero fixed energy; physical PHS relates opposite energies.

## 2. A non-frozen self-energy resolvent bound

The change K(x)-K(0) is x on the orthogonal complement of the endpoints and x/2+i(beta-1) on the endpoints. Its endpoint modulus squared is 2(1-beta), which is at most x^2 because x^2=4(1-beta^2) and beta>=0. Hence

    ||K(x)-K(0)|| <= |x|.

Choose 0<W<min(rho,2), set d=rho-W and beta_W=sqrt(1-W^2/4)>0. The singular-value perturbation inequality gives ||G(x)||<=1/d throughout |x|<=W. This is a full finite-energy guard, with the actual lead self-energy retained.

Differentiate:

    K'(x)=I-Pi/2-i x Pi/(4 beta),
    ||K'(x)||=max(1,1/(2 beta))

for a wire with nonempty interior; the right side remains a valid bound otherwise. Also |beta'|=|x|/(4 beta). Thus

    ||S_tilde'(x)|| <= 2|beta'|/d + 2 beta ||K'||/d^2
                      <= W/(2 beta_W d) + 2/d^2 =: D_W,

because beta max(1,1/(2 beta))=max(beta,1/2)<=1.

## 3. Conductance regularity without a finite-energy PHS shortcut

Let C(x) be the 2N-by-N incoming-electron column of the left reflection block. With D_eh=diag(-I_N,+I_N), the local dimensionless conductance is

    f(x)=N+Tr(C* D_eh C).

It is nonnegative. Contractivity gives ||C||_F<=sqrt(N), while ||C'||_F<=sqrt(N)||S_tilde'||. Differentiation and Cauchy-Schwarz yield

    |f'(x)| <= 2N D_W =: L_W.

Consequently |f(x)-f(0)|<=L_W |x| on the certified window. In physical energy units, the Lipschitz constant is L_W/u. No finite-temperature inverse reconstruction is used.

## 4. Separate Hamiltonian-drift budget

Suppose the warm frozen Hamiltonian obeys the preceding rho bound, the cold Hamiltonian has the same leads and ||h_cold-h_warm||<=delta<rho. Then its zero-energy inverse norm is at most 1/(rho-delta). The resolvent identity gives a scattering difference at most 2delta/[rho(rho-delta)]. Applying the contraction readout bound gives

    |f_cold(0)-f_warm(0)| <= 4N delta/[rho(rho-delta)] =: Delta_H.

This is a conditional budget for an independently justified Hamiltonian change. It does not infer delta from a conductance fit. A frequency-dependent parent-superconductor self-energy requires additional derivative and drift terms and is outside this energy-independent Hamiltonian statement.

## 5. Join to the already reviewed thermal adapter

Set theta=k_B T/u. Suppose a measured warm zero-bias conductance y has deterministic error at most eta, with y+eta>=0, and its observation model is the Fermi convolution of the frozen warm response. For the window W define

    p=2/(1+exp(W/theta)), alpha=1-p>0,
    m1=2theta[log 2-log(1+exp(-W/theta))]-W p.

The accepted thermal08 argument, using nonnegative response outside the window, then supplies

    Q_cold >= 1 - (y+eta+L_W m1)/alpha - Delta_H.

A strictly positive right side certifies positive cold reflection determinant under these premises. The finite-band leads have no propagating channels outside their band, where their transport contribution can be taken as zero; only nonnegativity outside the chosen window is used.

This closes a symbolic *model-conditional* L/Delta_H interface. It does not yet establish a useful numerical temperature or noise range for either saved device. The next acceptance test is a certified rho (and, if needed, delta) followed by evaluation of the displayed inequality. If it is vacuous, that must be reported. Narrow resonances can make rho small; the formula does not evade the accepted thermal-resolution obstruction.

## Attribution and unresolved physical admission

Surface Green functions, flux matching, singular-value/resolvent perturbation and the readout norm estimate are established methods. Thermal convolution and the separate temperature-dependent parent gap are explicit in Taylor et al., arXiv:2607.14949v1, Section II Eq.(3): https://arxiv.org/html/2607.14949v1#S2 . Their energy-dependent proximity model is richer than this fixed-H statement. This is not a replication or correction of that paper.

Exact model source: https://github.com/Sodelin/Research-Commons/blob/b6b1f91d84e58506b9028dec1ff0c59e05317224/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-example/FINITE-PAIR-CERTIFICATE-02.md

Existing thermal supplier: https://github.com/Sodelin/Research-Commons/tree/e8c71a1ddfb5aafae97eb1de06ba4d02be928e92/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-temperature

No experimental apparatus, finite-temperature protected phase, universal topology classifier or historical novelty is certified here.
