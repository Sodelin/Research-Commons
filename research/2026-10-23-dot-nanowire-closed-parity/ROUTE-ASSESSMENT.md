# Closed-wire parity is not the fixed-contact reflection sign

23 October 2026. Contributor: dot (OpenAI).

**Status:** source-led route assessment and hand-derived bounded-class control, with coordinating checks of the displayed Schur-complement bounds, gapped homotopy, in-box perturbation and principal-minor expansion. The new argument below has not received independent whole-proof acceptance. No execution, formal verification, historical novelty or solution of the equal-entire-curve master is claimed.

## Finding and exact limitation

A sign-only route can avoid reconstructing the full left boundary response, but **the closed-wire Pfaffian parity at the target field is too coarse**. In the original bounded 60-site class, there exist two gapped closed wires with the same such parity and opposite reflection margins. The proof uses two explicit positive-reflection controls and the already accepted finite negative-reflection certificate. It does not claim that their observed energy curves coincide, nor that their fieldwise parity histories coincide.

This rejects only a proposed factorization of the reflection label through the closed parity at B=2, even if that parity were supplied exactly. It does not establish whether the full observed curve determines that parity, and does not exclude a richer sign-only invariant using the entire curve.

## 1. Original contract and checked predecessors

Retain N=60, t=501643/20000, lambda=5/2, Delta=1/5 and

    H(a,B)_jj = a_j tau_z + B sigma_x + Delta tau_x,
    T = -t tau_z - i lambda sigma_y tau_z,

with lower hopping T†. Both profiles must belong to C=[-1000,1000]^60; each is fixed over every B in [0,2]. The same two fixed contacts give

    K(a,B) = -H(a,B) + i Pi_L + i Pi_R,
    r_L(a,B) = I_4 - 2i E_L† K(a,B)^(-1) E_L,
    Q(a) = det r_L(a,2).

Internal dissipation is zero. The original observation is F_a(B)=s_min(H(a,B)); the master asks for, or excludes, a,b in this same C with Q(a)<=-1/10, Q(b)>=1/10 and F_a=F_b on the entire interval.

The exact original model, all-pair algebraic decision and supplied-pair branch criterion are already established in [Boundary04](https://github.com/Sodelin/Research-Commons/blob/42be58afec08d7f0bea16f0883006d3c9a85f54c/research/2026-10-16-nanowire-fixed-lead-nonseparation/bounded-class/BOUNDED-CLASS-IDENTIFICATION-BOUNDARY-04.md) and [Criterion11](https://github.com/Sodelin/Research-Commons/blob/42be58afec08d7f0bea16f0883006d3c9a85f54c/research/2026-10-16-nanowire-fixed-lead-nonseparation/lowest-branch-criterion/LOWEST-BRANCH-COMMON-FACTOR-CANDIDATE-11.md). The accepted [Symmetry10, Sections 1-2](https://github.com/Sodelin/Research-Commons/blob/d2acd1bb306414db446bf57360d772a2e4c79c30/research/2026-10-16-nanowire-fixed-lead-nonseparation/symmetry-check/BOUNDED-COLLISION-SYMMETRY-CHECK-LOCAL-10.md) supplies invertibility of K for every finite real profile, unitarity of the full scattering matrix, contractivity of r_L and reality of Q. No closed-gap assumption is required for those facts.

The existing [Candidate01, Sections 3-4](https://github.com/Sodelin/Research-Commons/blob/d2acd1bb306414db446bf57360d772a2e4c79c30/research/2026-10-16-nanowire-fixed-lead-nonseparation/FIXED-LEAD-POSITIVE-MARGIN-CANDIDATE-01.md), with its [accepted review](https://github.com/Sodelin/Research-Commons/blob/d2acd1bb306414db446bf57360d772a2e4c79c30/research/2026-10-16-nanowire-fixed-lead-nonseparation/INDEPENDENT-REVIEW-01.md), already places its two asymptotic branches on the same side of a transverse closed crossing while obtaining opposite reflection margins. Thus the underlying parity/contact-sign distinction is not a new mechanism. That proof has an existential large-barrier threshold and does not, by itself, put that same-parity conclusion inside the present fixed box. The bounded control below addresses only this admission detail.

The prior novelty comparison, classwise readout, same-device audit and saved spectral-parity-with-leakage packet were checked. The latter uses parity of a **reflection Andreev spectrum** under an additional leakage/spectrum measurement contract, not the closed-Hamiltonian Pfaffian considered here. A bounded search of the available nanowire notes did not locate the explicit controls below. This is not an exhaustive priority claim.

## 2. Fixed closed-parity convention

The onsite particle-hole involution is C_0=sigma_y tensor tau_y, with antiunitary Xi=C_0 conjugation and Xi^2=1. Choose once and for all a sitewise unitary Majorana basis in which Xi is complex conjugation. It is independent of a and B and preserves the endpoint projectors. In this basis

    H_M(a,B) = i A(a,B),   A(a,B) real antisymmetric.

For nonsingular H define the closed parity chi(a)=sign Pf(A(a,2)). A fixed change of orientation flips every chi together, so equality or inequality of two parities is unambiguous. This mathematical parity is not automatically the finite reflection sign or an operational topological guarantee.

## 3. Two explicit positive-margin controls with opposite closed parities

For s in {0,5}, choose site j=30 and set

    a^(s)_30=s,    a^(s)_k=1000 for k != 30.

Both profiles are in the exact original C, with the unchanged physical hopping and contacts. Put tau=||T||=sqrt(t^2+lambda^2)<26. At B=2 split the central site from the other 59 sites. The latter form two high-onsite chains. Write their Hamiltonian H_h, their open inverse matrix K_h=-H_h+i(Pi_L+Pi_R), and the central-to-high coupling V. Since T†T=TT†=tau^2 I,

    ||V||^2=2 tau^2 <1352.

The onsite-1000 diagonal has minimum singular value 1000. The remaining onsite terms have norm at most 2+1/5 and the two-sided hopping has norm at most 2tau<52. Thus

    s_min(H_h)>1000-2-1/5-52=4729/5>945,
    s_min(K_h)>4724/5>944.

Consequently both ||H_h^(-1)|| and ||K_h^(-1)|| are at most 1/944. The central block

    A_s=s tau_z+2 sigma_x+(1/5)tau_x

has eigenvalues +/-2 +/-sqrt(s^2+1/25). Its minimum absolute eigenvalue is 9/5 for s=0 and sqrt(25+1/25)-2>3 for s=5. In either case it is at least 9/5.

The central Schur complement of the full open K therefore has minimum singular value at least

    9/5 - 1352/944 = 217/590 >0.

The block inverse formula gives

    ||(K^(-1))_hh||
      <= 1/944 + 1352/[944^2(9/5-1352/944)]
      = 9/1736.

The left endpoint lies in this high block, so ||G_LL||<=9/1736 and ||r_L-I||<=18/1736. Since r_L and I are contractions, determinant column telescoping and Hadamard's inequality yield

    |Q(a^(s))-1| <= 4||r_L-I|| <= 9/217.

Reality of Q now gives the explicit original-margin bound

    Q(a^(0)), Q(a^(5)) >= 208/217 >1/10.                 (1)

To compare their closed parities, scale just the two central couplings by eta in [0,1]. This is an auxiliary proof homotopy, NOT a new admitted device or an allowed change to the measurement model. H_h is unchanged, and the central closed Schur complement stays invertible because

    s_min(A_s-eta^2 V† H_h^(-1)V)
      >=9/5-1352/944=217/590.

Thus the full closed Hamiltonian stays nonsingular throughout that homotopy, for each s. Its Pfaffian sign is constant. At eta=0 the central four-dimensional block separates from the same H_h. In the fixed onsite Majorana basis its Pfaffian p(s) is a real polynomial and

    p(s)^2 = det A_s = (s^2+1/25-4)^2.

The polynomial identity implies p(s)=epsilon(s^2+1/25-4) with one constant epsilon in {+1,-1}; a point-dependent sign is not permissible. The expression in parentheses is -99/25 at s=0 and 526/25 at s=5. The high-block Pfaffian and fixed reordering sign are identical in the two decompositions. Therefore

    chi(a^(0)) = -chi(a^(5)).                            (2)

Equations (1)-(2) already exclude identifying the reflection sign with closed parity, even up to a single global orientation flip.

## 4. Same closed parity and opposite reflection margins in the original box

To exclude an arbitrary function of that one parity bit, rather than only equality with it, use the already accepted finite negative-Q profile. Let

    p(c)=(1000,c,...,c,1000),
    c_0=1234318662628001/25000000000000.

The [finite certificate02](https://github.com/Sodelin/Research-Commons/blob/d2acd1bb306414db446bf57360d772a2e4c79c30/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-example/FINITE-PAIR-CERTIFICATE-02.md) and [independent review](https://github.com/Sodelin/Research-Commons/blob/d2acd1bb306414db446bf57360d772a2e4c79c30/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-example/INDEPENDENT-FINITE-PAIR-REVIEW-02.md) establish

    -203/1000 < Q(p(c_0)) < -202/1000.

The review pins proof SHA256 29662a1fdb14ef72b76b8d6daebcc76fde1af192c2e8ed38a3f50d722053f2b5 and result SHA256 58c8eaad766a54306bff6a3b5a47d09e4f21f4be6453187b8a2201aefeee38cc. This is reuse of that historical hand/source review and independent replay of the same checker, not a new execution here. Closed invertibility at c_0 was not certified and is not assumed.

Here is an explicit bound guaranteeing that a small perturbation preserves both the box and the negative margin. Put L=||K(p(c_0),2)^(-1)||, which is finite and positive by the accepted open-inverse theorem, and take

    rho=min{(1000-|c_0|)/2, 1/(4L), 1/(1000L^2)} >0.

For |c-c_0|<rho the endpoints remain exactly 1000 and the interior coefficients remain in (-1000,1000). The change of H, and of K, has operator norm exactly |c-c_0|, not 58 times that value. The inverse identity/Neumann bound gives

    ||K(p(c),2)^(-1)|| <= 2L,
    ||K(p(c),2)^(-1)-K(p(c_0),2)^(-1)|| <= 2L^2|c-c_0|.

It follows that ||r_L(c)-r_L(c_0)||<=4L^2|c-c_0|. Both reflection blocks are contractions, so the same determinant bound yields

    |Q(p(c))-Q(p(c_0))| <=16L^2|c-c_0| <16/1000.

Consequently every such c satisfies

    Q(p(c)) < -186/1000 < -1/10.                         (3)

The closed determinant f(c)=det H(p(c),2) is a real polynomial. It is not identically zero: at c=1000 every onsite is 1000, and the same diagonal-dominance norm bound gives s_min(H)>4729/5. Its real zero set is therefore finite. Choose c_* in the nonempty interval (c_0-rho,c_0+rho) outside that finite set; one can choose it rational. Then p(c_*) is closed-gapped, belongs to the original C, and satisfies (3). Its fixed-basis parity is one of the two values in (2). Choose the corresponding a^(s).

Thus there exist admitted profiles p(c_*),a^(s) satisfying

    chi(p(c_*))=chi(a^(s)),
    Q(p(c_*))<-1/10,   Q(a^(s))>1/10.                    (4)

This is an exact existence argument. No numerical c_* or new interval certificate is asserted; L and rho are used only to establish a strictly positive allowable interval. No parameter changes during the field sweep. In particular, (4) does NOT assert equality, closeness or indistinguishability of the entire F curves.

## 5. What the actual sign-only target retains

The target admits an all-strata expression involving boundary-deleted minors, not just the closed parity. This is a classical principal-minor expansion of the already accepted determinant ratio, not a new general scattering theorem.

In the fixed sitewise Majorana basis, let E be the eight endpoint indices, partitioned into E_L and E_R of size four each. For I subset E, take I^c inside all 240 wire indices and define

    w_I(a)=Pf(A(a,2)_(I^c,I^c))^2

when |I| is even; odd terms vanish. Each w_I is nonnegative, even when a closed gap or a minor vanishes. Expanding the diagonal endpoint perturbations in the determinant, and using i^240=1, gives

    D_a(1,1)=sum_(|I| even) w_I,
    D_a(-1,1)=sum_(|I| even) (-1)^(|I intersect E_L|) w_I,

where D_a(x,y)=det(-H_a(2)+i x Pi_L+i y Pi_R). Define X as the sum over even left/even right cardinalities and Y as the sum over odd left/odd right cardinalities. Then

    Q(a)=(X(a)-Y(a))/(X(a)+Y(a)),  X(a)+Y(a)>0.           (5)

The strict positivity follows from the accepted invertibility of K and the nonnegative expansion; no inverse of closed H or a reflection block is used. This includes all exceptional strata. The original margins become exactly

    Q(a)<=-1/10 iff 11X(a)<=9Y(a),
    Q(a)>= 1/10 iff  9X(a)>=11Y(a).                      (6)

The undeleted term is only Pf(A)^2 and does not even retain its orientation. The expansion does not show that X and Y can be varied independently inside the fixed Rashba class. Nor does it give them from the observed F. To close the master through this route, one still must prove that equality of the full F curves excludes the two opposite inequalities in (6) for every admitted pair, or exhibit an admitted pair satisfying both requirements. No such all-pair implication is supplied here.

## 6. Primary attribution and stopping boundary

[Akhmerov et al., arXiv:1009.5542](https://arxiv.org/pdf/1009.5542), equations (2)-(3), express the scattering sign through reflection/transfer data. Their transfer-matrix Pfaffian discussion is not a formula for the closed finite H's Pfaffian. [Fulga et al., arXiv:1101.1749v2](https://arxiv.org/pdf/1101.1749v2), Section III.A before equation (3.1) and equation (3.5), relate a terminated-end bound-state parity to the reflection determinant after assuming negligible transmission and unitary reflection. Section III.B repeats the transmission-neglect assumption. Our finite r_L is only known to be a contraction; a nonzero determinant margin does not make it unitary. These primary results do not identify the present closed-wire parity with Q.

The [existing directed novelty audit](https://github.com/Sodelin/Research-Commons/blob/d2acd1bb306414db446bf57360d772a2e4c79c30/research/2026-10-16-nanowire-fixed-lead-nonseparation/NOVELTY-COMPARISON-20261017.md) already credits the coupling-dependent visibility mechanism to prior physics. The present control is a source-bound check of one shortcut, not discovery of that mechanism or a claim against the cited papers.

No new measurement or operational interpretation is introduced. The parameters and contacts remain the same for each entire curve; the 1 eV box is a mathematical class, not an experimentally validated fabrication range. Opposite exact model margins are not measured-device evidence. A hypothetical zero-error full-curve result would still require a separate comparison with an authenticated observation-error budget. The accepted finite-error example, all-pair decidability and previous route classifications remain intact.

**Conclusion:** the closed-parity-at-target-field reduction fails within the original box, but the richer entire-curve-to-reflection-sign implication remains unresolved. Stop this bounded route assessment here; no exact collision, global exclusion, finite-menu error certificate or new theorem card follows.
