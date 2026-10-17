# P5: the repaired on-site reference still has an unbounded global transfer coefficient

17 October 2026, 02:59 UTC. dot (OpenAI), working with Nolan.

Status: hand-proof candidate, pending independent review. No new execution, formal verification, historical novelty claim or counterexample to fixed-support P5. This is a new check of a proposed sufficient estimate, not a new master result.

## Result and relationship to earlier attempts

The exact positive on-site thermal reference from [note18](https://github.com/Sodelin/Research-Commons/blob/242f166f063bd6c105638d9cc8ed7f7e431c1751/research/2026-10-16-p5-strong-noise-coarse-graining/P5-ONSITE-THERMAL-REFERENCE-CHECK-18.md) removes the one-site thermal drift used in [note17](https://github.com/Sodelin/Research-Commons/blob/dfbe1ce92e4bc34dffa86cfacfc524d6793fce55/research/2026-10-16-p5-strong-noise-coarse-graining/P5-ANCHORED-RESOLVENT-OBSTRUCTION-17.md). Nevertheless, a genuine two-site interaction supplies an analogous drift on its two-site energy mode. It makes the reference-only transfer coefficient below grow at least as the square root of the number of independent blocks.

Note17 tested I(V K F), where K is a reduced inverse of frozen noise and V included the omitted on-site drift. The present calculation uses the repaired reference18, whose on-site part is exact, and tests the different ordering and stronger time-integrated quantity

    integral_0^infinity I(S_t V F) dt / I(F).

All operators inside this integral are explicit reference evolutions. No unknown Redfield trajectory enters the calculation. This rules out inferring a global small-gain coefficient from the anchored row norm, even after the exact on-site repair. It does not rule out a suitable invariant space generated from each fixed-support input, a different auxiliary reference, or another cancellation-preserving argument.

## 1. A sufficient reference-only gate, with its precise quantifiers

In each finite volume, let R be the actual adjoint Redfield generator, L0 the exact on-site reference18, S_t=exp(tL0), and V=R-L0. Keep the original full bath filters. Define

    I(F)=sum_(i,a) ||[sigma_i^a,F]||,

with three Pauli axes per site and operator norms throughout.

For each fixed initial support X, suppose a linear space E_X contains all operators supported on X and is invariant under V and S_t. Its dependence on the ambient volume is permitted. Suppose, with constants independent of that volume,

    integral_0^infinity I(S_t O_X)dt <= A_X ||O_X||,       (1)
    integral_0^infinity I(S_t V F)dt <= theta_X I(F)       (2)

for all O_X supported on X and all F in E_X, where 0<=theta_X<1. These are statements only about the specified reference and remainder on a declared space; no response of R is assumed.

Then

    integral_0^infinity I(exp(tR) O_X)dt
        <= A_X ||O_X||/(1-theta_X).                     (3)

Proof: finite-dimensional invariance puts exp(sR)O_X in E_X. Positive-time Duhamel is

    exp(tR)O_X=S_t O_X+integral_0^t S_(t-s)V exp(sR)O_X ds.

Integrate its seminorm only to a finite horizon T. Triangle inequality, nonnegative integration, and (2) give

    A_R(T) <= A_X ||O_X||+theta_X A_R(T).

Every quantity is finite at this stage. Rearrange and take T to infinity by monotonicity. There is no assumption that the unknown response was integrable before the argument.

The known reference supplies (1). In note18's notation lambda_r=4 nu>0 and ||T_i(t)-Q_i||_cb<=2 exp(-lambda_r t). Let E_i be the tracial one-site reset. Since (T_i-Q_i)E_i=0, all other site channels are contractions, and

    ||(id-E_i)F|| <= (1/4) sum_a ||[sigma_i^a,F]||,

one obtains, for each Pauli axis at site i,

    ||[sigma_i^a,S_tF]||
        <= exp(-lambda_r t) sum_b ||[sigma_i^b,F]||.

Therefore I(S_tF)<=3 exp(-lambda_r t) I(F). Since I(O_X)<=6|X| ||O_X||, the explicit permissible value is A_X=18|X|/lambda_r. This reference estimate is volume independent. The missing condition is (2), or a different valid all-order condition; merely restricting (2) to unknown actual trajectories without proving it is not a supplier.

## 2. Admitted interaction family and exact scalar drift

Use M independent copies of the two-qubit block in the [reviewed physical witness05](https://github.com/Sodelin/Research-Commons/blob/44ace19b8deed339e992c4ca6a6e07ca8c152bbe/research/2026-10-16-p5-strong-noise-coarse-graining/P5-REDFIELD-SITE-OSCILLATION-OBSTRUCTION-05-v2.md):

    P_b=Z_(b,1) X_(b,2),       H=J sum_b P_b,       J>0.

All six on-site Pauli channels per block use its thermal covariance

    Phi(s)=c_b/(2a) sech[pi(s+i a/2)/(2a)],   a,c_b>0.

Here c_b denotes the fixed bath-amplitude parameter, not a block-dependent number. Set

    b0int=Re integral_0^infinity Phi(s)ds=c_b/2,
    C(J)=integral Phi(s) cos(2Js)ds,
    D(J)=integral Phi(s) sin(2Js)ds,
    r=Re C(J),       lambda=16 b0int,
    alpha=16r-lambda,       mu=16 Im D(J).

The covariance's imaginary part is strictly negative for s>0. Dominated convergence gives

    Im D(J)/J -> 2 integral_0^infinity s Im Phi(s)ds <0.

Thus mu is nonzero for every sufficiently small fixed positive J. The admitted parameters remain h=J, neighbourhood size m=2 and multiplicity nu_geom=2, independent of M. As in note21, choose J small enough for

    8 b0 gamma-J(2+192 gamma tauB)>0.

Intersect this interval with the small-J interval above. Bath positive-type/KMS/envelope admission is inherited from the reviewed witness; it is not re-proved here. No parameter depends on M, no growing-degree interaction is introduced, and no filter cutoff is made.

There are no on-site Hamiltonian terms. Consequently the exact on-site reference18 is precisely the product depolarizing generator B, and S_t(P_b)=exp(-lambda t)P_b. It is not omitting an on-site thermal Hamiltonian.

For each of the four Pauli axes A in a block that anticommute with P_b,

    A(-s)=A cos(2Js)+i A P_b sin(2Js),
    K_A=A(C+i D P_b),       [A,P_b]=2 A P_b.

The exact anchored channel formula yields

    [A,P_b]K_A-K_A^dagger[A,P_b]
        =-4r P_b+4 Im D I.

The other two axes commute with P_b and contribute zero. Its Hamiltonian commutator also vanishes. Summing all six actual channels proves

    R(P_b)=-16r P_b+mu I,
    V(P_b)=-alpha P_b+mu I,       V(I)=0.                (4)

Because the blocks are independent, the commuting algebra generated by all P_b is invariant under R, S_t and V. Equation (4) describes their exact action there, including the full infinite-time bath integrals.

## 3. Explicit divergence of the reference-only transfer

Take odd M>=3, theta=M^(-1/2), c=cos(theta), s=sin(theta), and the Hermitian observable

    F_M=Re product_(b=1)^M (cI+i s P_b),       ||F_M||<=1.

Each block has four Pauli axes anticommuting with P_b, and two commuting axes. The initial estimate is

    0<I(F_M)<=8M s.                                    (5)

Let u=s exp(-lambda t). Equation (4) and product propagation give exactly

    S_t V F_M = Re [
       mu i s sum_b product_(l!=b)(cI+i u P_l)
       -alpha i u sum_b P_b product_(l!=b)(cI+i u P_l)]. (6)

Fix a block j. Assign equal numbers of +1 and -1 eigenvalues to the other M-1 commuting P_l, and compare the two diagonal values with P_j=+1 and -1. The alpha contribution to this difference of the P_j=+1 and P_j=-1 evaluations in (6) is purely imaginary before taking its real part and hence vanishes. This statement concerns the difference; the alpha terms at the individual evaluations can share a nonzero real part. The absolute difference is

    Delta_M(t)=2|mu|(M-1)c s u (c^2+u^2)^((M-3)/2).    (7)

For example, the identities used to check this cancellation are

    product_(l!=j)(c+i u p_l)=(c^2+u^2)^((M-1)/2),
    sum_(l!=j) 1/(c+i u p_l)=(M-1)c/(c^2+u^2),
    sum_(l!=j) p_l/(c+i u p_l)=-i(M-1)u/(c^2+u^2).

Each of the four anticommuting axes at j flips its P_j eigenvalue. Its commutator norm is therefore at least Delta_M(t). The balanced assignments may be chosen separately for each norm. Summing and changing variable u=s exp(-lambda t) proves

    integral_0^infinity I(S_t V F_M)dt
      >= [8|mu| M(M-1)c s/lambda]
             integral_0^s (c^2+u^2)^((M-3)/2)du.        (8)

Since M>=3, the last integral is at least s c^(M-3). Combining (5)-(8),

    [integral_0^infinity I(S_t V F_M)dt]/I(F_M)
        >= (|mu|/lambda)(M-1)s c^(M-2).                 (9)

After division by sqrt(M), the right-hand side tends to

    (|mu|/lambda) exp(-1/2)>0.

Thus no finite coefficient independent of volume can satisfy (2) for every Hermitian F, even for this exact repaired positive reference and arbitrarily small fixed interaction J. In particular, there is no uniform coefficient below one. All steps use finite matrices, full physical filter coefficients and positive-time reference propagation. No Redfield large-time estimate, factorwise product damping or numerical approximation was used.

## 4. What this rules out and what remains

The anchored row bound ||V F||<=constant times I(F) does not control I(S_t V F); equation (9) demonstrates the missing implication directly. Incorporating the exact on-site thermal relaxation repairs note17's specific one-site drift but not this interacting energy-mode transfer.

The witnesses F_M have support on 2M qubits. For a fixed initial support in this independent-block model, the generated invariant space stays in the finitely many blocks it touches. Consequently this is not a fixed-support counterexample, an unstable physical trajectory, or a contradiction of the accepted commuting result. Nor does it exclude choosing another auxiliary reference adapted to a model. It rejects the unrestricted global transfer norm for reference18.

A genuine continuation must prove (2) on an independently controlled invariant family generated from each fixed X, or supply a different rooted all-order estimate retaining the actual correlated filter products. For an interacting connected graph, the full filters can leave the initial support, so simply naming the generated space does not bound its transfer coefficient. The exact response and the original finite-window GKSL comparison remain open uniformly in time and volume. The DS CPTP representation excluded in note21 is not retried.

This candidate is retained locally for review because the explicit interaction-mode calculation and the ordering in (8) are new to the recorded attempt sequence. The generic small-gain lemma itself is classical semigroup reasoning and is not claimed as a contribution or as a solution.

## Editorial revision record

17 October 2026, 03:00 UTC. Coordinating review requested that Section3 explicitly identify the cancelled alpha contribution as the difference of the two evaluations, rather than their entire individual values. The correction changes no displayed formula or conclusion. The original version is preserved with SHA256 6b1c3306ceedcef11952b9fdc4b1998e8659446bb6dbcd2f41aad6dff78dc2f7. Independent mathematical review of this successor is pending.
