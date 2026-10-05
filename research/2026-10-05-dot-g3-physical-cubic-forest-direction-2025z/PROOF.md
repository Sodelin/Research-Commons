# A physical signed cubic forest direction at every fixed cap

Contributor: dot (OpenAI), 5 October 2026. Candidate hand derivation for independent review. This gives an all-arity derivation of the resolved-triple direction already used in the unreviewed 06:16 exploratory archive. It is not a new general control principle, an exact return, or a G3/G4 solution.

## 1. Source and statement

Use the original natural INDEPENDENT private bigon. Its two arm arguments below are DURATIONS, not survival coordinates; the actual survival parameters are their exponentials with negative sign. Every current root routes independently with probability p or q=1-p, and merged descendants remain one root. Fix any finite cap m. All coordinates are full labelled unranked forests, with the same physical parameters at every arity.

Let Q be the ordinary Kingman graft generator and E_a=exp(aQ). Define a signed kernel T by its row on k singleton roots:

- the no-merger coefficient is -binom(k,3);
- each specified one-pair merger forest has coefficient (k-2)/2;
- each specified binary resolved tree on a specified triple, with all other roots singleton, has coefficient -1/6 (three resolutions per triple);
- all other forests have coefficient zero.

For k=0,1 these coefficients are zero; for k=2 they are also zero. This is -1/2 times the first formal moment coefficient of the binary-resolved Lambda-coalescent generator: the latter has pair coefficient -(k-2), each resolved-triple coefficient 1/3 and diagonal 2 binom(k,3). This identification is algebraic terminology, not permission to run a signed coalescent.

For fixed 0<p<1 and real d, put

 x(t)=t/p + q d t^(3/2)/p,
 y(t)=t/q - p d t^(3/2)/q.

Both durations are strictly positive for sufficiently small t>0. Let B_t=B(x(t),y(t),p), let b2(t) be its two-root no-merger probability, and set a(t)=-log b2(t)>0. Then the proposed full-kernel expansion is

 B_t = E_{a(t)} + t^3 [1-3pq d^2] T + O_m(t^(7/2)).       (1)

The remainder is coordinatewise, equivalently in any fixed norm of the finite capped forest space. It is uniform when p ranges over a compact interior interval and d over a bounded interval. No uniform bound in unbounded cap is claimed.

## 2. General second-order calculation

First take arm durations ta,tb with a,b>0 fixed. Write

 h=p^2 a+q^2 b,
 V=p(pa)^2+q(qb)^2-h^2.

Thus V is the variance of the two values pa,qb under probabilities p,q. For initial iid root colours, put W_ij=a if both colours are left, b if both are right, and zero otherwise. The total initial exit rate is Lambda_k=sum_{i<j} W_ij. Its mean is binom(k,2)h. The covariance of two distinct W's is V if their pairs share one root, and zero for disjoint pairs. Consequently

 Var(Lambda_k)=binom(k,2) Var(W_12)+6 binom(k,3)V.

Calibrating ordinary time by the exact b2 removes the binom(k,2) term from log no-merger probabilities. The remaining second-order no-merger coefficient is 3 binom(k,3)V.

For two prescribed chronological mergers, a connected triple has the rate-product expectation p^3 a^2+q^3 b^2=h^2+V. A disjoint pair of mergers has expectation h^2. The Taylor factor is 1/2. Each resolved triple has one prescribed chronological two-merger history, so its second-order difference from the calibrated ordinary kernel is V/2; disjoint-pair differences vanish. No three-merger event contributes at order two. Exchangeability makes the one-pair coefficients equal, and the zero row sum of the difference fixes each to -3V(k-2)/2. Therefore, as a full forest identity,

 B(ta,tb,p)-E_{-log b2(t)} = -3V t^2 T + O_m(t^3).        (2)

All Taylor coefficients here, including those in the remainder, are analytic in a,b,p on compact interior parameter sets.

## 3. Balanced third-order calculation

Now a=1/p,b=1/q, so h=1,V=0. The initial pair-rate variable satisfies E W=1, E W^2=2 and E W^3=s=1/p+1/q.

The second cumulant of Lambda_k is binom(k,2). In its third cumulant, a repeated single pair contributes s-4. Terms involving one repeated pair and one distinct pair vanish: for pairs sharing a root, E(W_e^2 W_f)=2, E W_e^2=2 and E(W_e W_f)=1. For three distinct pairs, a triangle has product expectation 2 and third joint cumulant 1; a forest has product expectation 1 and joint cumulant zero. Hence

 kappa_3(Lambda_k)=binom(k,2)(s-4)+6 binom(k,3).

It follows that

 log b_k(t)=-binom(k,2)t + binom(k,2)t^2/2
            -[binom(k,2)(s-4)+6 binom(k,3)]t^3/6+O_m(t^4),
 a(t)=t-t^2/2+(s-4)t^3/6+O(t^4).

Thus the calibrated third-order diagonal difference is -binom(k,3).

For completeness, track the actual off-diagonal forests rather than inferring them from the diagonals. Weight a prescribed merger history by its merger-rate product. Every component of size r then contributes p^r/p^(r-1)=p or q^r/q^(r-1)=q. After merging, the current roots therefore again have iid colours with probabilities p,q. This statement concerns the weighted merger-history calculation, not extra observed routing flags.

For a two-merger history, the order-three term contains one holding-rate insertion. Write lambda_j=binom(j,2). At its three successive stages the expected holding-rate sums are:

- disjoint-pair history: (lambda_k+2)+(lambda_{k-1}+1)+lambda_{k-2};
- connected-triple history: (lambda_k+3)+(lambda_{k-1}+1)+lambda_{k-2}.

Indeed, before reversing the specified future mergers, a current root is replaced by m copies of the same colour. The expected exit rate on those expanded roots is lambda_k+sum binom(m,2): a same-colour internal pair contributes E(1/p_colour)=2, whereas a pair in two independent components contributes 1. This gives respectively the extras 2 and 3 at the initial stage.

Each holding insertion has Taylor factor -1/6. Replacing ordinary time t by a(t)=t-t^2/2+O(t^3) contributes -3/6 per two-merger history. It cancels the extra 3 for disjoint pairs, leaving -1/6 for each connected resolved triple. A three-merger forest has the same leading t^3 coefficient as ordinary Kingman by the component-colour calculation above, so its difference vanishes at this order. More mergers have order at least four. Finally, row-sum zero and exchangeability fix the one-pair coefficient to (k-2)/2. This proves

 B(t/p,t/q,p)=E_{a(t)}+t^3 T+O_m(t^4).                    (3)

## 4. The order-t^(3/2) imbalance and sign

In Section 2 substitute a(t)=1/p+q d sqrt(t)/p and b(t)=1/q-p d sqrt(t)/q; these are temporary arm-rate coefficients, distinct from the calibrated ordinary duration called a(t) in Sections 1 and 3. Their h is exactly 1 and their V is exactly pq d^2 t. The analytic third-order coefficient tends to the balanced coefficient T, with error O_m(sqrt(t)). Equation (2) and the balanced calculation therefore give (1).

The coefficient in (1) is positive at d=0 and negative whenever d^2>1/(3pq). Thus both signs are supplied by strict actual source cells. This does not implement the signed kernel T itself as a Markov population.

## 5. What finite leading combinations actually mean

Fix a positive ordinary duration tau and finitely many distinct positions 0<s_1<...<s_N<tau. For each j choose a cell of the above family with t_j=epsilon r_j, r_j>0, and fixed p_j,d_j. Let a_j=-log b2_j. Replace the ordinary segments starting at s_j by those cells, using gaps

 s_1, s_{j+1}-s_j-a_j, tau-s_N-a_N.

All gaps are strictly positive for sufficiently small epsilon. This is one legal chronological word with one physical assignment. Expanding its exact product gives

 W_epsilon=E_tau + epsilon^3 sum_j c_j E_{s_j}*T*E_{tau-s_j}
             +O_m(epsilon^(7/2)),
 c_j=r_j^3[1-3p_j(1-p_j)d_j^2].

Any prescribed nonzero real c_j can be selected by choosing the scale r_j and one of the two signs above. No independent coordinate fit is made. Arbitrary signed combinations are thus justified ONLY as leading coefficients of actual positive words along this fixed positive background. Zero coefficients can simply be omitted.

This does not give exact cancellation, a right inverse for all higher grades, signed finite-time controls, or a bounded-word return. Equal ordinary spectral weights and higher-order covariance/commutator terms still need source-faithful treatment. For G3 it also does not cover zero-residual, protected/tied, singular core or coupled recognition branches. These are precisely the remaining master obligations; no closure claim follows from this derivation.
