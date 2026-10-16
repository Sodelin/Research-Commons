# Fixed-beta two-local shell encoding with counted physical overhead

16 October 2026. Derivation by dot (OpenAI) for Nolan. Complete hand-proof candidate awaiting independent review. No novelty, Lean, execution or P1 closure claim. This is a proposed import of established classical two-distribution closeness hardness. All original physical qubits and inverse-temperature constraints are counted.

## Claim and supplier

Fix beta>0. For sufficiently large logical s, put D=binom(s,2). Fix 0<epsilon<=1/4 and L=max{D^(2/3)/epsilon^(4/3),sqrt(D)/epsilon^2}, eta=1/(100L). The construction below uses exactly N=sm+R physical qubits, with integers m,R chosen using only s,epsilon,beta, independently of the unknown distributions. All nonidentity Pauli coefficients of H have magnitude at most one and locality at most two. At known inverse temperature beta, equality versus trace-norm separation at least epsilon needs Omega(L) worst-case TOTAL copies, even for collective/adaptive access to the two unknown Gibbs states.

For fixed beta and fixed epsilon, m=O_beta(log s), R=O_beta(s sqrt(log s)), so N=O_beta(s log s) and N>=s. In particular this gives an admitted sequence of physical sizes with lower bound Omega_beta(N^(4/3)/(log N)^(4/3)) at constant accuracy. Extension to every sufficiently large physical N is by independent maximally mixed spectators and choosing the largest constructed size that fits; the parameter choices must be fixed by a monotone explicit ceiling rule if that extension is used. The displayed sequence claim does not rely on that extra step.

Supplier: Chan, Diakonikolas, Gregory Valiant, Paul Valiant, SODA2014 Theorem1.1. Two unknown D-symbol distributions, equal versus L1 distance greater than 2epsilon, require Omega(L) samples. Primary source: https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf and https://arxiv.org/abs/1308.3946. This testing result is prior work. The physical encoding below is the candidate to review.

## 1. Positive logical energy and block averages

For an unknown distribution p on unordered pairs {i,j} of [s], smooth pbar=(3/4)p+(1/4)U_D. Set v_ij=-log pbar_ij, so 0<=v_ij<=V=log(4D).

Use m physical bits per logical site. Let w_i in {0,...,m} be the number of ones in block i and x_i=w_i/m. Fix

lambda=16 log(2s/eta), mu=beta/2,
E_p(x)=lambda(sum_i x_i-2)^2 + sum_{i<j}v_ij x_i x_j,
J_p=E_p(x)+mu sum_i w_i(m-w_i).

Both summands of E_p are nonnegative for all fractional block averages x_i in [0,1]. Every term in J_p is a polynomial of degree at most two in the physical bits. On a constant block configuration x_i in {0,1}, the lock penalty vanishes. On the shell sum_i x_i=2, exactly one pair term survives, so its energy is v_ij and the total shell partition weight is sum exp(-v_ij)=1. The desired ideal state is therefore: sample pbar_ij, set precisely blocks i and j to all ones and every other block to all zeros.

Choose the integer m sufficiently large to satisfy all of

m>=2,
m^2 >= (lambda+V/2)/beta,
mu m^2 >= 32 log(2s),
sm exp(-mu m/4)<=1,
4s^3 m exp(-mu m/4)<=eta/4.

These conditions are explicit and feasible; for fixed beta, m=O_beta(log(s/eta)) suffices. One may choose the least satisfying integer for the present sequence claim.

## 2. Leakage of the cloned state

First consider constant blocks outside the two-block shell. If their logical weight is w, their energy is at least lambda(w-2)^2. Thus their total partition weight is at most

sum_{w !=2} binom(s,w) exp(-lambda(w-2)^2)
 <= 2s^2 sum_{a>=1} s^a exp(-lambda a)
 = 2s^3 exp(-lambda)/(1-s exp(-lambda)) <= eta/4.

Here binom(s,w)<=s^w, and for w=2-a the same bound s^(2+a) is an overestimate; lambda as selected gives the final inequality for s>=2, eta<=1.

For nonconstant blocks, round each block to a nearest constant bit, resolving ties by a fixed rule. Let w be the number of rounded-one blocks and q=sum_i min(w_i,m-w_i)>=1 the total minority-bit count. For each rounded bit string there are at most binom(sm,q) configurations with that q. Also

|sum_i x_i-w|<=q/m,
mu sum_i w_i(m-w_i)>=mu m q/2.

Write a=|w-2|. Split the latter lock bound into two equal halves. If q<ma/2 then the positive square in E_p is at least lambda a^2/4. If q>=ma/2 then the second half of the lock penalty is at least mu m^2 a/8. Consequently

J_p >= mu m q/4 + g(a),
g(a)=min{lambda a^2/4,mu m^2 a/8}.

For a>=1, the choices above imply g(a)>=4a log(2s). Hence

sum_w binom(s,w) exp(-g(|w-2|))
 <= s^2+2s^2 sum_{a>=1}s^a(2s)^(-4a) <=2s^2.

The total nonconstant-block partition weight is therefore at most

2s^2 sum_{q>=1}binom(sm,q)exp(-mu m q/4)
 <=2s^2[exp(sm exp(-mu m/4))-1]
 <=4s^3 m exp(-mu m/4)<=eta/4.

The q-count overestimates incompatible roundings and ties, which is harmless. Both leakage bounds are uniform in p. Since the shell partition is exactly one, the Gibbs distribution proportional to exp(-J_p) has TV distance at most eta/2 from the ideal encoded pbar. Crucially, this count keeps the logical weight suppression; the invalid crude factor 2^(sm) is never used.

## 3. Pair coefficients and the remaining fields

Use physical Z_j=1-2y_j and write J_p=c_p+K_p(z)+F_p(z), where K_p is a sum of pair terms, F_p=sum_j h_j z_j, and c_p is constant. The lock contributes pair coefficient -mu/2 inside a block and no linear term. The square contributes lambda/(2m^2) to every pair of distinct physical sites. The v term contributes v_ij/(4m^2) between blocks i,j. Thus every pair coefficient has absolute value at most

mu/2+lambda/(2m^2)+V/(4m^2)<=3beta/4.

For a site in block i the field coefficient is

h_j= -lambda(s-4)/(2m) - (1/(4m))sum_{l != i}v_il.

In particular |h_j|<=Hmax=lambda(s+4)/(2m)+(s-1)V/(4m), and

sum_j |h_j| <= S0=s lambda(s+4)/2+s(s-1)V/4.

The large fields cannot simply be declared admitted. The next construction implements them using bounded pair coefficients and additional physical reservoir spins. All bounds depend only on s,epsilon,beta, not p.

## 4. Pinned reservoir and its exact phase symmetry

Let gamma=beta/2 and h0=beta/4. Choose integer R satisfying

R>=8,
R^2>=8S0/gamma,
R>=Hmax/beta,
2h0 R>=log(8/eta),
R exp(-gamma R/2)<=1,
2R exp(-gamma R/2)<=eta/16.

Such choices have R=O_beta(s sqrt(log(s/eta))+log(s/eta)) for fixed beta. Introduce R spins a_l in {-1,+1} and define the dimensionless total energy

Q_p(z,a)=K_p(z)+(1/R)F_p(z)sum_l a_l
          -gamma sum_{l<t}a_l a_t -h0 sum_l a_l.

There are no logical one-body terms left. Logical pair coefficients have magnitude <=3beta/4, reservoir pairs have magnitude gamma<=beta, cross pairs have magnitude |h_j|/R<=beta, and reservoir fields have magnitude h0<=beta. All coefficients of H_p=Q_p/beta therefore obey the original unit bound, with locality two. Removing any identity coefficient does not affect the Gibbs state.

Conditioning on every reservoir spin being +1 gives exactly the distribution proportional to exp(-J_p), because Q_p(z,+)=J_p(z)-c_p plus a p-independent reservoir constant. No assumptions about the sign of h_j are used.

Let Z_+ and Z_- be the partition contributions of the all-plus and all-minus reservoir configurations. Since K_p(-z)=K_p(z) and F_p(-z)=-F_p(z), a global logical spin flip gives exactly

Z_-=exp(-2h0 R) Z_+.

This identity controls the competing reservoir phase; ignoring it would leave an incorrect two-phase approximation.

For a reservoir configuration with l minus spins, its energy minus that of the all-plus reservoir at the same logical z is

2gamma l(R-l)+2h0 l -(2l/R)F_p(z).

For 1<=l<=R/2 this is at least gamma l R-2lS0/R >=gamma l R/2. For l>=R/2, set q=R-l and compare instead with the all-minus reservoir at the same z. The difference is at least

gamma q R-2qS0/R-2h0q >=gamma q R/2,

using R^2>=8S0/gamma and R>=8. Thus mixed reservoirs contribute at most

(Z_++Z_-)[exp(R exp(-gamma R/2))-1]
 <=(Z_++Z_-)2R exp(-gamma R/2).

Double-counting the middle layer is harmless. The non-plus reservoir partition weight relative to Z_+ is consequently at most

exp(-2h0R)+(1+exp(-2h0R))2R exp(-gamma R/2)
 <= eta/8+(1+eta/8)eta/16 < eta/4.

Hence the complete Gibbs distribution exp(-Q_p)/Z has TV distance at most eta/4 from the cloned Gibbs distribution with the reservoir pinned plus. Together with Section2, its TV distance from the ideal sample-only encoded pbar with reservoir all-plus is less than eta. This is a finite-temperature estimate at the given fixed beta, not a zero-temperature substitution.

## 5. Testing transfer with physical qubits counted

For p=q the two constructed Hamiltonians and Gibbs states are identical. If ||p-q||_1>2epsilon, smoothing leaves L1 separation greater than 3epsilon/2. The two ideal encoded distributions have the same separation, and the two TV approximation errors contribute at most 4eta to the L1 loss. Thus the actual Gibbs states are at least epsilon apart.

The ideal encoded state is sampled using only a sample from p (with probability 3/4) or a known uniform pair (with probability 1/4), followed by copying its bits into the m-sized blocks and setting the known reservoir bits plus. No value p_ij, Hamiltonian coefficient or partition function is queried by this simulator. The construction of H_p proves admission, but need not be computable from the sample oracle by the reduction.

Every constructed state is diagonal. Full computational-basis samples dominate any collective quantum measurement: conditional on the sampled bit strings, a quantum measurement is just its known Born-rule stochastic postprocessing. Thus a Gibbs tester with worst-case total budget T can be simulated with at most a constant times T source samples even under adaptive source allocation. For T<=L, replacing the actual sources by their ideal encoded approximations changes the entire transcript by TV at most T eta<=1/100 (hybrid argument). Constant amplification then contradicts the classical closeness lower bound if T=o(L). If T>L the claimed lower bound is automatic.

The error convention, full trace norm and worst-case TOTAL budget are preserved. Merely expected stopping budgets and runtime efficiency are not asserted. The physical size N=sm+R includes every clone and reservoir spin; there is no uncounted ancillary Gibbs resource.

## Scope and remaining review gates

This is a candidate fixed-beta lower bound for the original class through its classical two-local subfamily. For k>=2 the same two-local family is admitted, but its exponent need not beat the dense k>=3 lower. It would sharpen the fixed-beta k=2 floor if independently accepted. It would not settle the fixed-beta optimal-copy gap or the quantum single-copy/collective gap. Check each counting inequality, reservoir phase comparison, parameter overhead and the exact total-copy reduction before changing any accepted-bound register. The standard ferromagnetic locking and field-gadget methods require a focused prior-work audit before any novelty statement.
