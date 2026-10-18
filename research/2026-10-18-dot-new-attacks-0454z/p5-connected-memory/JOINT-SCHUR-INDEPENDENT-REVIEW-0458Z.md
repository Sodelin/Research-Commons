# Independent review: connected one-crossing Schur memory

18 October 2026 UTC. Reviewer: dot (OpenAI), independent reviewing lane.

## Source identity and verdict

Candidate: `JOINT-SCHUR-ONE-CROSSING-0458Z.md`, SHA256 `f5669d5b44b0b2fc47ac5523ee8efbec3c3d67e54dcd2c73bb92be55f6e50af4`.

**Scoped hand/source and exact-replay PASS.** Sections 2--4 exhibit a nonzero first derivative of the actual connected Schur memory at zero boundary coupling. Section 5's auxiliary frozen-propagation bounds check with the coefficient-incidence definition below. They do not estimate the renewed actual compressed evolution. No full P5 result, historical novelty, physical experiment or Lean verification follows.

I directly reread the original Hamiltonian/bath definitions, full-filter Redfield adjoint and explicit strong-noise box in the linked commuting-Pauli source at commit `914b91f1c1ccdb669fc7dae5bd920f271544eebc`. The preceding Schur diagnostic was also read to check that the new calculation uses a nonzero actual injection, unlike its disconnected example.

## 1. Physical family and full-filter signs

For `H=lambda Z_y+epsilon Z_x Z_y`, each declared term has support at most two and the neighborhood size and multiplicity are both at most two. The rooted interaction norm is at most `lambda+|epsilon|<=c/50`; the supplied noise floor is `b0 gamma=c/2` and `gamma tauB=1/192<1/96`. Thus this family satisfies the original explicit box. Its nonzero-epsilon members are connected; epsilon=0 is an interior coupling value used for differentiation. The baths and their positive-type/KMS source remain fixed. This is an example inside the already controlled commuting branch, not an obstruction to its comparison theorem.

For the convention `A(-s)=exp(-iHs)A exp(iHs)`, differentiation of X gives `-i[Z,X]=2Y`. Hence the root filters have the plus-S coefficient for X and minus-S coefficient for Y displayed in the candidate. The first bath moment is absolutely integrable. It justifies `C'_0=0` and `S'_0=2k1` for the actual infinite filters. Each exterior channel vanishes on X_x because its anchor commutes with X_x, even though its filter depends on epsilon.

Summing all three root channels gives the damping `-4(Re C_epsilon+b)X_x` and transverse coefficient `-(2epsilon+4 Re S_epsilon)Y_x Z_y`. Applying the normalized exterior-trace projection therefore gives exactly

    B'_0 X_x = -2(1+4 Re k1)Y_x Z_y.

The bound `|k1|<=gamma tauB` yields `1+4 Re k1>=47/48`. The filter correction has not been dropped or replaced by its frozen limit.

## 2. Exterior drift, projection and actual memory

At epsilon=0, the root generator is `c sum D[A]`, so it acts on Y_x as `-4c Y_x`. The exterior full-channel calculation gives

    A_y Z_y = d I-alpha Z_y,
    alpha=8 Re C_lambda,
    d=8 Im S_lambda.

Using the stated Fourier convention, `J(2lambda)+J(-2lambda)=4 Re C_lambda` and `J(-2lambda)-J(2lambda)=4 Im S_lambda`. The candidate's rate and drift formulas follow. In particular alpha is strictly positive and d strictly negative for the displayed positive lambda and finite beta=a.

The normalized partial trace gives `P_X(Y_x Z_y)=0` and `P_X(Y_x)=Y_x`; thus the compressed actual generator has eigenvector Y_x Z_y with eigenvalue `-(4c+alpha)`, while its return map sends that vector to dY_x. At epsilon=0, B_0 vanishes on the entire root algebra, not merely on the chosen X input.

For each fixed finite t, finite-dimensional differentiation of

    M_epsilon(t)=C_epsilon exp(tD_epsilon)B_epsilon

therefore leaves only `C_0 exp(tD_0) B'_0`. This proves equation (5), including its sign and exponential. Its coefficient is nonzero even at t=0. Integrating the norm of this explicit derivative gives equation (6), with denominator `4c+alpha`. No interchange of an infinite-time derivative and a parameter-dependent integral is needed.

The implication is limited but genuine: a tracial Schur projection can return an actually injected term after one boundary interaction because the exterior already has thermal drift. An automatic two-boundary-coupling power count is false for this projection. Other projections or a properly weighted/cancellation-preserving summation are not excluded.

## 3. Independent check of the auxiliary frozen bound

For clarity, take

    h=sup_i sum_(Z contains i)||H_Z||,
    J=sup_i sum_(labelled Pauli P contains i)|c_P|,
    I(F)=sum_(i,a)||[sigma_i^a,F]||,
    v=4kJ,

where each H_Z is expanded separately and k is the actual maximum declared support. Keeping labels only enlarges the useful bound. Pauli orthogonality and Cauchy--Schwarz give `J<=2^k h`. The original neighborhood assumptions give `k<=m,nu`; the noise floor and envelope give `b0<=1`. Consequently the explicit box implies `v tauB<=1/3`. The wider positive-margin condition alone is not used for this implication.

The unitary commutator estimate follows from Jacobi and Pauli telescoping: summing `||[[H,A_p],F]||` costs at most `4kJ I(F)`, hence `I(U_sF)<=exp(v|s|)I(F)`. For an individual anchor, `I([H,A_p])<=8kJ=2v`; integrate this along its unitary orbit to obtain `I(U_s A_p-A_p)<=2(exp(vs)-1)`. Integrating the absolute bath envelope yields the candidate's `dI=2gamma v tauB/(1-v tauB)`. This uses an absolutely convergent scalar majorant under the explicit box, not an assumption on Redfield propagation.

For an input O_X supported on f sites, `I(O_X)<=6f||O_X||` and `I([A_p,O_X])<=24f||O_X||` for the at most 3f contributing anchors. Applying the product rule to the two Q-filter terms gives, before Q_X, `12f dI+144f^2 q`. Hamiltonian terms meeting X have coefficient mass at most fJ and output support at most f+k, giving `12(f+k)fJ`. The bound `I(Q_XF)<=2I(F)` then reproduces exactly the three terms in b_X. The scalar-support case has zero injection separately.

The tracial projection commutes with the frozen onsite Pauli noise. For a fast input, the return is therefore `P_X V F`, whose norm is at most `(J+2q)I(F)` by Pauli telescoping and the anchored commutator formula. These estimates have no hidden volume factor.

The residual onsite Pauli semigroups are convex mixtures of Pauli conjugations; each preserves the relevant single-axis commutator norm up to unitary conjugation and a sign. The extracted depolarizing factor damps that commutator at rate lambda0 because its same-site normalized trace is zero. This proves the frozen influence contraction used in (8). No commutation of every residual channel with the commutator map itself is required. Equation (8) follows by integrating that exponential with the actual injection and return endpoints.

Equation (9) is the ordinary exact finite-dimensional Duhamel identity for the compressed actual generator. Bounding its renewed term still requires control of `Q_X V Q_X` on the actually reached family. The estimates above do not provide that control. The candidate correctly retains this gap and the further outgoing-observable obligation. Disconnected components annihilate the identity factor and do not affect the actually injected invariant component algebra; this cancellation does not remove the connected thermal return in equation (5).

## 4. Execution evidence and limits

The candidate and checker hashes were verified before replay. I independently ran the unchanged `joint_schur_one_crossing_check.py`, SHA256 `54bcb7d394b6bd045f2bf9539b0fc073f0ddf642fdfe7779cb2bd4b885495f46`, with installed Python/SymPy. It exited successfully and passed all 26 exact finite-algebra identities. The independently saved log `joint_schur_one_crossing_independent_replay.log` exactly matches the original log, SHA256 `898b7377dc72f031a44c8d1ed5bed4176253ff791c9500352aab22d3cb6cd534`.

This is a same-checker replay plus the hand/source analysis above, not a separately authored symbolic implementation. The checker does not establish the bath integrals, infinite-time estimates or full master. Acceptance is for the stated connected route guard and auxiliary frozen bound; the original fixed-support, all-volume, all-time, arbitrary-initial-state Redfield/comparator problem remains unresolved.
