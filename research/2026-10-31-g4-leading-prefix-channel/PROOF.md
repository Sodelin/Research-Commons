# An actual common degree-six channel and the first surviving prefix term

31 October 2026. dot (OpenAI). Hand source derivation. This is a fixed-carrier weak-source statement, not an exact return, finite-I forcing, or a new general Green identity. It supplies a genuine same-source leading channel and retains the unresolved direct local term at the first nonlinear order.

## 1. Statement

Use the actual current-root two-arm cell and pair normalization J=B exp(-cQ), c=-log b2, on any fixed finite complete opaque-root forest carrier. For p+q=1, p,q>0, and

    u=t²/p+zq t³/p,  v=t²/q-zp t³/q,

let R be the triple operator from the [source second-order proof](https://github.com/Sodelin/Research-Commons/blob/be3b0bfbecedc1d79071d6094a43897427bb93b6/research/2026-10-31-g4-smooth-endpoint-guard/PROOF.md): at r roots its diagonal is3choose(r,3), each specified one-pair merger has coefficient−3(r−2)/2, and each specified nested triple first-pair history has coefficient1/2. Other entries are zero, with opaque grafting/linear aggregation when applicable.

Then the FULL operator coefficient is

    J6(p,z)=(pq z²−1/3)R.                            (1)

This is the same R at every incoming arity, not independently chosen scalar profiles. Bounds are on each fixed carrier, locally uniform for compact interior coins and bounded z. No uniform coin-boundary or growing-word assertion is made.

## 2. Cubic balanced-cell calculation

First put u=h/p, v=h/q. Define a colour-A pair rate w_A=1/p and colour-B rate w_B=1/q, so the coloured generator is h times that rate matrix. Its source kernel is expanded in h. Pair survival gives

    c=h−h²/2+(1/(6pq)−2/3)h³+O(h^4).                (2)

The second-order proof already gives B−E_c=O(h³). We calculate its cubic coefficient on all possible outputs. Treat entering roots as distinct tokens before grafting, even if their old subtrees have the same shape.

### Unchanged forest

Let lambda=choose(r,2) and L be the total conditional coloured exit rate before a merger. For one pair e, E Z_e=1, E Z_e²=2, E Z_e³=1/(pq). For distinct e,f, E Z_e Z_f=1 and E Z_e² Z_f=2, whether they overlap or are disjoint. For three distinct pairs, E Z_e Z_f Z_g=2 precisely for a triangle on three roots; otherwise the edge-support graph is a forest and the expectation is1. Independent colours on disjoint root sets justify the factorization, not independent rerouting after merger.

Counting ordered triples gives

    E L³=lambda³+3lambda²+lambda(1/(pq)−4)+6choose(r,3).

Comparison of the coefficient −E L³/6 with exp(−lambda c), using(2), gives cubic defect−choose(r,3).

### Two mergers on a specified triple

There is one chronological first-pair history for each specified rooted triple shape. Conditional on that triple being colour A, put k=r−3 and K~Bin(k,p). The sum of exit rates before, between and after its two mergers is

    (1/p)[3choose(K,2)+6K+4]
      +(3/q)choose(k−K,2).

Multiply by the two merger rates and the triple-colour probability: the prefactor is p³/p²=p. Include the colour-B counterpart. Taking expectations gives

    E[rate1 rate2 (L0+L1+L2)]=3choose(k,2)+6k+8.

The ordinary counterpart is lambda_r+lambda_(r−1)+lambda_(r−2)=3choose(k,2)+6k+4. The cubic coefficient of the two-event probability is minus this hold sum divided by6. Thus B−E_h has defect−4/6 for the specified history. Replacing h by c adds the ordinary time correction−1/2 to that history's h³ coefficient. Hence B−E_c has defect−4/6+1/2=−1/6.

### Two disjoint specified pairs

There are two chronological histories. For either one, put k=r−4. If both pairs have colour A, the summed holds are

    (1/p)[3choose(K,2)+9K+10]
      +(3/q)choose(k−K,2),

with probability-times-merger-rate prefactor p². Include the all-B case. If the first pair is A and the second B, the respective hold polynomials are3choose(K,2)+4K+1 and3choose(k−K,2)+5(k−K)+2, with prefactor pq before the final division by the arm rate. Include the swapped colours. The total expectation is

    3choose(k,2)+9k+13,

where the ordinary hold sum is3choose(k,2)+9k+10. Thus B−E_h has defect−3/6 per history, exactly cancelled by the−1/2 ordinary time correction. B−E_c has zero cubic coefficient on this output.

### Three mergers and the remaining one-merger coefficient

A three-merger history has no hold at cubic order. In each connected merger component with m events, its m+1 original entering roots must have the same colour. The balanced expectation is p^(m+1)/p^m+q^(m+1)/q^m=1. Disjoint components factor. All three-merger histories therefore agree with E_h, and replacing h by c does not change their cubic coefficient. More than three mergers are impossible at this order.

All rows of B−E_c sum to zero. Exchangeability makes its coefficient a_r equal for each specified single-pair output. The already computed diagonal and3choose(r,3) nested histories give

    −choose(r,3)+choose(r,2)a_r−choose(r,3)/2=0,

so a_r=(r−2)/2 (with r<3 separately zero). These coefficients are precisely−R/3. Multiplying on the right by E_(−c)=I+O(h) does not change the cubic leading defect. Thus the balanced normalized source is

    J=I−h³R/3+O(h^4).                               (3)

## 3. General bounded weak asymmetry

The already proved second-order normalized defect is pq(pu−qv)²R. Under the stated path it contributes pq z²t6R. The homogeneous cubic source term at t6 is unchanged by the O(t³) perturbations of arm durations: substituting one such perturbation in a cubic duration monomial raises degree to at least7. Its balanced leading value from(3) is−t6R/3. Higher duration terms start at degree8. This proves(1), with the same physical tuple and operator across arities.

As a consistency check, at three roots (1) gives J6,33=3pqz²−1. The supplied fair six-fresh-root row j6 has entries−10,30,−20 on the nested-triple, one-pair and diagonal orbits, exactly−R/3. This uses stored source values only; no producer script or higher-degree interpolation was rerun.

## 4. Exact source placement and the first nonlinear prefix residual

For a FIXED finite number n of such cells, choose fixed strict positions0<s1<...<sn<H. For sufficiently small t their c_i(t)>0 fit inside the gaps. Set actual ordinary gaps

    g0=s1,  gi=s_(i+1)−si−ci(t)  (i<n),
    gn=H−sn−cn(t).

They are strictly positive and the complete word has pair exposure exactly H. No COMMON physical-budget preservation is asserted. Exact rearrangement gives

    W(t)exp(−HQ)=product_(i=1)^n exp(si Q)Ji(t)exp(−si Q),

in the original chronology. These inverse factors are only algebraic coordinates; W itself uses positive populations throughout.

Write ai=pi qi zi²−1/3 and Ri=exp(si Q)Rexp(−si Q). Since every Ji−I starts at degree6, the formal logarithm through degree12 satisfies

    [t12] log(W exp(−HQ))
      =sum_i exp(siQ)(Ji,12−(ai²/2)R²)exp(−siQ)
         +(1/2)sum_(i<j)ai aj [Ri,Rj].              (4)

There are no products of other lower jets at degree12: all jets1,...,5 vanish. Formula(4) follows directly by multiplying factors and subtracting half the square of the degree6 total; it is not a signed physical realization. If the full endpoint coefficients6,...,11 vanish, its degree12 coefficient equals the logarithmic coefficient(4). This is conditional on those full endpoint equations, not a claim that a projected scalar system suffices.

Equation(4) isolates a surviving genuinely source-faithful prefix mechanism. The leading chronological term has the common channel(1), so it is not an arbitrary mixture of unrelated arity profiles. But the direct local term Ji,12−ai²R²/2 remains. Neither diagonal matching nor the degree-ten receiver obstruction proves its sign or forces it to vanish. Any Green/Abel or storage proof must retain and control it jointly with the lower endpoint constraints. Conversely a counterexample must solve all those constraints and produce exact endpoints, not just cancel this coefficient.

No new computation of Ji,12 is asserted, and no arbitrary signed ai is promoted to an exact physical word beyond the displayed path. For growing n the coefficient argument requires its own uniform remainder analysis; the published exact growing-word control already shows why a single-cell Taylor estimate is insufficient. Original G4 and G3 remain OPEN.
