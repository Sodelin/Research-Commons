# P1: the forward-relative-entropy partition over-resolves transverse directions

20 October 2026. dot (OpenAI), working with Nolan. Scoped hand proof with a separate assistant-context review. No historical novelty or full P1 rate claim. All logarithms are natural.

## 1. Precise claim and original scope

The saved state-partition attempt greedily selects a center from a finite Gibbs prior, assigns all remaining candidates with D(rho_i||rho_center)<=M/n to its cell, and repeats. Each cell is represented by its physical prior mixture. Its distortion bound is valid, but its required conditional-information bound is not automatic.

**Theorem (scoped partition obstruction).** At fixed beta=2,k=2, there are admitted N-qubit finite priors and the single sequence n=N^20 such that every cell of this greedy construction is a singleton, independently of ordering, and

    H(G|C_n) >= (r/2) log N - O(r) = Omega(M log N),
    r=binom(N,2),  M=3N+9r.

Here C_n is the actual n-copy quantum experiment. Moreover, for root fidelity f(rho,sigma)=||sqrt(rho)sqrt(sigma)||_1, its actual-group overlap sum satisfies

    log sum_(g,h) sqrt(p_g p_h) f(Omega_g,Omega_h)
      >= (r/2) log N - O(r).

Thus both proposed uniform O(M) conditional entropy and exp(O(M)) overlap bounds FAIL for this particular partition. The claim is not a lower bound against the original P1 testing problem or against other state-sensitive kernels. Indeed this same family satisfies chi_(2n)=O(M), and the fixed vacuum reference already has squared Bures risk O(M/n).

All unknown inputs retain the original coefficientwise bounded, unrestricted-degree Gibbs promise, with fixed known beta. No coefficients or beta grow. n denotes paid original copies in C_n. There is no classical posterior assumption, LAN approximation, or iterated fixed-N-then-n limit.

Current scope source: https://github.com/Sodelin/Research-Commons/blob/0bd558cf151b3c7dfdc8c6de5c446c70c8b95f29/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md . Accepted upper13/lower32 and the full P1 master remain unchanged.

## 2. Hamiltonians and one simultaneous scaling

Let |vac> be the all-plus Z basis vector. Set

    H0 = -1/2 sum_i Z_i -1/2 sum_(i<j) Z_i Z_j,
    Delta = 2(N-1),  n=N^20,
    V_x = sum_(a={i,j}) lambda_a X_i X_j,
    lambda_a = -Delta x_a/sqrt(n),   x in [-1,1]^r,
    H_x=H0+V_x,   rho_x=exp(-2 H_x)/Z_x.

All background coefficients are -1/2, every transverse coefficient obeys |lambda_a|<=2/N^9, and all other allowed coefficients vanish. Thus all candidates are admitted for N>=2.

A basis vector with s flipped spins has excitation energy

    E_s-E_vac=s(N-s+1).

The vacuum is the unique ground state, its gap is N, and every two-flip vector |a> has energy Delta above it. Define the uniform operator bound

    R = r Delta/sqrt(n),   ||V_x||<=R.

R=O(N^-7). In all following inequalities N is sufficiently large that R<=N/4 and the explicit conditions stated below hold.

## 3. Uniform forward-relative-entropy separation

Write psi(lambda)=log Tr exp[-beta(H0+sum lambda_a X_a)], retaining beta in this section before setting beta=2.

### 3.1 A dimension-free derivative bound

For arbitrary Hermitian perturbation directions A,B,C, Duhamel differentiation and Schatten Holder give

    |D^j Z[A_1,...,A_j]| <= beta^j Z product_l ||A_l||,
       j=1,2,3.

Indeed each ordered trace integrand has exponential factors exp(-t_l beta H), with t_l>=0 and sum t_l=1. Holder bounds its absolute value by Z times the product of the inserted operator norms; the sum of simplex volumes over derivative permutations is one. Differentiating log Z gives one third-derivative term, three second-times-first terms, and two first-derivative products. Hence

    |D^3 psi[A,B,C]| <=6 beta^3 ||A|| ||B|| ||C||.         (1)

In particular, along a segment whose perturbation has norm at most R,

    |D^2 psi_lambda[A,A]-D^2 psi_0[A,A]|
       <=6 beta^3 R ||A||^2.                             (2)

### 3.2 Diagonal Hessian at H0

The Hessian in the pair-flip directions is diagonal. A product of two distinct pair flips changes a nonempty set of Z bits, so its trace against diagonal factors vanishes. Means of all X_a vanish. In a diagonal Hessian entry, the transitions vacuum<->a contribute

    2 beta (p_vac-p_a)/Delta,

and all other contributions are nonnegative. Here p_a=e^(-beta Delta)p_vac. Put c_N=p_vac-p_a; c_N tends to one and is at least 3/4 for sufficiently large N. Therefore, for delta_lambda,

    D^2 psi_0[delta_lambda,delta_lambda]
       >=(2 beta c_N/Delta)||delta_lambda||_2^2.          (3)

For x,y in the entire cube, ||sum(delta_lambda)_a X_a||^2<=r||delta_lambda||_2^2. The exact Bregman integral and (2)-(3) imply

    D(rho_x||rho_y)
      >= [beta c_N/Delta-3 beta^3 R r] ||delta_lambda||_2^2.

If

    c_N>=3/4,  3 beta^2 r^2 Delta^2/sqrt(n)<=1/4,          (4)

then uniformly for ALL x,y in the cube,

    D(rho_x||rho_y) >= beta Delta/(2n) ||x-y||_2^2.       (5)

Condition (4) holds eventually with beta=2 and n=N^20: its nonconstant left side is O(N^-4). This is a uniform finite-N Taylor remainder estimate, not merely a pointwise asymptotic expansion. It applies in both directions, although only forward divergence is needed.

## 4. A finite packing forces every greedy cell to be a singleton

Set

    s^2=4M/(beta Delta),  beta=2.

Use the finite grid in [-1,1]^r with coordinate mesh 1/N^2. Greedily retain a grid point and remove all grid points at Euclidean distance <=s from it until none remain. Let the resulting finite set be X_N, with cardinality K. Retained pairs have distance >s. Every point of the continuous cube is within s+sqrt(r)/(2N^2)<=2s of a retained point. Thus, writing v_r for the unit Euclidean ball volume,

    K v_r(2s)^r >=2^r,
    K >= [sqrt(r)/(s sqrt(2 pi e))]^r,                   (6)

where v_r<=(2 pi e/r)^(r/2), from the elementary Gaussian integral bound. Since r/s^2=beta Delta r/(4M) is asymptotic to N/9,

    log K >= (r/2)log N-C0 r                              (7)

for a universal constant C0 and all sufficiently large N. Fix the uniform prior on this finite set.

By (5), every distinct pair has D(rho_x||rho_y)>2M/n, hence certainly >M/n. Consequently the saved greedy forward-D partition produces K singleton cells for EVERY ordering. Actual group states are precisely Omega_x=rho_x^{tensor n}, not substituted center approximations. G=Theta and H(G)=log K.

## 5. Uniform ground-vector bounds from a resolvent

Let E_x and |psi_x> be the ground energy and normalized ground vector of H_x, with vacuum overlap real positive. Weyl gives a simple ground state and gap at least N-2R. Write

    |psi_x>=a_x |vac>+q_x,  q_x perpendicular to vacuum,
    A0=Q(H0-E_vac)Q,
    A_x=A0+QV_xQ-(E_x-E_vac)Q.

Because |E_x-E_vac|<=R and A0>=NQ, A_x>=N-2R>=N/2. The ground equation gives

    q_x=-a_x A_x^(-1) V_x|vac>.

Since V_x|vac>=-(Delta/sqrt n)sum_a x_a|a>,

    ||V_x|vac>|| <=Delta sqrt(r)/sqrt(n),
    ||q_x|| <=2 Delta sqrt(r)/(N sqrt(n)),
    n||q_x||^2 <=16r.                                   (8)

Let P_pair project onto the r two-flip vectors and Q_out=I-|vac><vac|-P_pair. As A0^(-1)V_x|vac> lies exactly in P_pair, the resolvent identity yields

    ||Q_out psi_x||
      <= ||A_x^(-1)-A0^(-1)|| ||V_x|vac>||
      <=(4R/N^2)||V_x|vac>|| <=4R^2/N^2.

Thus

    n||Q_out psi_x||^2 <=16n R^4/N^4
                         <=256 r^4/n =: eta_N.          (9)

These inequalities hold uniformly over the entire parameter cube. eta_N=O(N^-12).

## 6. Actual finite-n pure-copy entropy, without LAN

Let Xi_m=E_x (|psi_x><psi_x|)^{tensor m}, for m=n or 2n. This density matrix is supported on the finite symmetric tensor subspace Sym^m(C^(2^N)). Map its occupation basis isometrically to the Fock occupation basis for the nonvacuum modes by omitting the vacuum occupation, which is determined by m minus the other occupations. This is an isometry, NOT a partial trace that discards coherence between occupation numbers.

For a bosonic mode of mean occupation u, entropy is at most

    g(u)=(u+1)log(u+1)-u log u.

This follows directly by comparing with the normalized geometric distribution/operator of mean u in relative entropy. Comparing with the product of such operators bounds a multimode state's entropy by the sum of g of its mean occupations, without an independence assumption. Concavity of g allows aggregation over each set of modes.

By (8)-(9), for m=n the r pair modes have total mean occupation <=16r, and the D=2^N-r-1 other modes have total mean occupation <=eta_N. Therefore

    S(Xi_n) <= r g(16)+D g(eta_N/D)
       <= r g(16)+eta_N[1+log(1+D/eta_N)]
       = r g(16)+o(1).                                 (10)

If D=0 the second term is omitted; asymptotically D>0. For m=2n, the same argument gives

    S(Xi_(2n)) <=r g(32)+o(1).                           (11)

The discarded-mode entropy is O(N^-11+N^-12 log N), not its dimension times a trace error. The estimates are exact entropy upper bounds for finite-n copies of the actual perturbed ground vectors.

## 7. Thermal impurity remains negligible for the same n=N^20

At H0 and beta=2, the excited relative partition weight obeys, for N>=3,

    Q0 <=(N+1)e^(-2N)+2^N e^[-4(N-1)].

The s=1 and s=N configurations contribute the first term; every remaining s has energy at least 2(N-1). Weyl gives, uniformly over x,

    1-<psi_x|rho_x|psi_x> <= epsilon_N:=e^(4R) Q0.        (12)

This is also the half trace distance from rho_x to its ground projector. Tensoring and averaging imply that the half trace distance between omega_m=E rho_x^{tensor m} and Xi_m is at most m epsilon_N. For m=n or 2n, this tends to zero. The entropy continuity inequality in dimension 2^(mN) gives

    S(omega_m) <= S(Xi_m)+h_2(m epsilon_N)
                                +m^2 N log 2 epsilon_N. (13)

The entire correction tends to zero because m is polynomial in N and epsilon_N is exponentially small. Dropping the nonnegative component entropies yields

    chi_n <=r g(16)+o(1),
    chi_(2n) <=r g(32)+o(1).                             (14)

This explicitly controls the actual mixed Gibbs copies, including the growing Hilbert-space dimension. Beta, coefficient bounds, n, packing, perturbation error, and impurity all use the same simultaneous N sequence.

## 8. Conditional-information obstruction and its exact limit

The partition is singleton, so (7),(14) give

    H(G|C_n)=log K-chi_n
       >=(r/2)log N-[C0+g(16)]r-o(1)
       =Omega(M log N).                                (15)

Thus no constant depending only on beta,k can bound this particular partition's conditional entropy by M. It is an admitted failure of the saved state-sensitive construction, not a generic dimension-only example.

The physical task is not hard at that scale. From (8),(12),

    1-<vac|rho_x|vac> <=16r/n+epsilon_N,
    d_B^2(rho_x,|vac><vac|)
      =2[1-sqrt(<vac|rho_x|vac>)]
      <=32r/n+2epsilon_N.                              (16)

This fixed known reference uses no unknown copies and already has O(M/n) Bures loss on the constructed family. Also 0<=chi_(2n)-chi_n<=chi_(2n)=O(M). Neither (15) nor the overlap statement below refutes the desired full-class rate.

## 9. The actual-group overlap attack, and why it also fails here

For any ensemble p_g,Omega_g on a common space, form block row A=(sqrt(p_g)sqrt(Omega_g))_g and Gamma=A* A. Let Delta_G denote pinching by g. Spectral identities give exactly

    H(G|C)=S(Delta_G Gamma)-S(Gamma)
          =D(Gamma||Delta_G Gamma).

For each off-diagonal block B=Gamma_gh, the block matrix

    [[sqrt(BB*), -B],[-B*,sqrt(B*B)]]

is positive semidefinite, as follows from an SVD. Add its diagonal blocks to the corresponding blocks of Delta_G Gamma, for every unordered pair, to obtain a block-diagonal T>=Gamma with

    Tr T=1+sum_(g!=h)||Gamma_gh||_1
         =sum_(g,h)sqrt(p_g p_h) f(Omega_g,Omega_h)=:L.

The last identity follows from the definition of the Gram blocks. The minimum relative entropy over block-diagonal reference states is D(Gamma||Delta_G Gamma). Since Gamma<=T and log is operator monotone on support,

    H(G|C) <=D(Gamma||T/L)<=log L.                        (17)

Singular Gamma is harmless by support restriction or positive regularization. This is block-coherence/robustness machinery, not a new measurement or a novelty claim.

Equation (15) already forces log L=Omega(M log N). There is also a direct overlap check: (8) and common positive vacuum phases imply |<psi_x|psi_y>|>=1-128r/n for all x,y, using the norm triangle inequality (the constant is deliberately loose). Let w_x=<psi_x|rho_x|psi_x> and w_y=<psi_y|rho_y|psi_y>. Purify the two ground components with the same ancillary flag, and the two excited remainders in disjoint flag sectors. Uhlmann's bound then gives f(rho_x,rho_y)>=sqrt(w_x w_y)|<psi_x|psi_y>|. Since both weights are at least 1-epsilon_N, this implies

    f(rho_x,rho_y)>=(1-epsilon_N)(1-128r/n).

For sufficiently large N, tensor multiplicativity and log(1-u)>=-2u give

    f(rho_x^{tensor n},rho_y^{tensor n})
       >=exp[-256r-2n epsilon_N].

With the uniform singleton prior,

    L_n >=K exp[-256r-2n epsilon_N],
    log L_n >=(r/2)log N-O(r).                           (18)

So the hoped-for exp(O(M)) overlap supplier fails sharply in the very family above, rather than merely remaining unproved.

## 10. Sources, verification status, and exact conclusion

- Rana, Parashar, Winter and Lewenstein, *Logarithmic coherence: Operational interpretation of l1-norm coherence*, Phys. Rev. A 96,052336 (2017), https://arxiv.org/pdf/1612.09234 , Theorem 7, Eq.(8), and Appendix E, establish the ordinary coherence/robustness logarithmic upper-bound method. Section 9 gives its needed block-matrix proof directly. This is prior machinery, not an asserted new inequality.
- Audenaert, *A Sharp Fannes-type Inequality for the von Neumann Entropy*, https://arxiv.org/abs/quant-ph/0610146 , supplies the finite-dimensional entropy continuity estimate used with the explicitly charged mN-qubit dimension in (13).
- The geometric-distribution entropy bound in Section 6 is proved by a direct relative-entropy comparison; no asymptotic quantum Gaussian theorem is invoked. The resolvent and log-partition derivative estimates are derived above.
- The included independent assistant-context review reports scoped PASS for the producing candidate. The presentation-only changes and exact reviewed/final hashes are recorded separately. Its 3,982 exact bounded scalar/combinatorial checks and the producer's seven floating scalar-bound evaluations are not the asymptotic proof, packing construction, entropy simulation, external peer review, or Lean verification. No broad literature novelty review is claimed.

The chosen actual-mixture overlap route is exhausted for the saved greedy forward-D partition: its necessary conditional-information bound and its stronger overlap bound are false. Other partitions or kernels with mixed-state references may avoid this over-resolution; none is constructed here. No improved or worsened full P1 bound follows. The included review accepts only this scoped obstruction.
