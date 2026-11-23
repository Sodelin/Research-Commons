# G4 v4: near-ordinary COMMON controls COMMON, not BOTH

This is a scoped hand theorem and counterexample for the same matched private current-root E/B grammar as v1–v3, now allowing unequal positive arms. A finite source word has strict clocks 0<q0,q1<1 and interior route coins 0<g<1. Projection is a comparison of forest kernels, not an assertion that arbitrary original interfaces furnish their readouts. In particular, comparisons refer to the labelled forest/merger state after a segment, not to recorded continuous merger times or hidden arm annotations.

## Quantitative Jensen bound

For one cell let X be q0 with probability g and q1 with probability 1−g. Put μ=E X and Var=g(1−g)(q0−q1)². Its COMMON pair and triple no-merger factors are μ and E X³. The exact identity is

    E X³−μ³ = Var (q0+q1+μ) ≥ 2μ Var.

Proof: expand E[(X−μ)²(X+2μ)], use E X=μ, and evaluate the expectation over the two arms. Also q0+q1≥μ. Ordinary factors make no contribution to the normalized Jensen defect. For a whole word write C=b2_COMMON and J=b3_COMMON/C³−1. Diagonal factors multiply in both arities, so

    1+J = ∏ (1+η_i),    η_i=(E X_i³−μ_i³)/μ_i³ ≥ 2 Var_i/μ_i²,
    Σ g_i(1−g_i) ((q0_i−q1_i)/μ_i)² ≤ J/2.

This controls an arm mismatch weighted by the physical coin, uniformly in the number of cells. It does not by itself control the largest unweighted mismatch (rare coins are allowed), or the sum of the absolute mismatches.

## Positive result: a uniform finite-arity COMMON proxy

Project each population mixture in a COMMON cell to E(μ), and keep ordinary fragments unchanged. The product of the projections is E(C), by the coalescent semigroup. For forests with at most n entering roots, their COMMON labelled-forest kernels have total variation at most

    min{1, M_n J/8},
    M_n = max over 1≤r≤n  Σ_{k≤r} Σ_λ |A_{r,k,λ}| λ(λ−1).

Here the ordinary root-count probabilities are the finite polynomials p_{r,k}(q)=Σ_λ A_{r,k,λ}q^λ at the integer Kingman death rates λ ∈ {choose(k,2),…,choose(r,2)}. Explicit coefficients are the usual partial fractions of the pure-death equations; the checker implements them.

For completeness, the waiting time in state k has rate choose(k,2), independent of the uniformly chosen pair. Thus for fixed entering labelled forest and exactly r−k mergers, the distribution of the merger sequence, and therefore the resulting forest, is independent of q. Write this conditional kernel Q_{r,k}. Each ordinary row is consequently the mixture of Q_{r,k} with weights p_{r,k}(q). Taylor at μ cancels the first derivative on averaging q0,q1, and gives an absolute weight difference at most Var/2 times sup over [0,1] of |p''_{r,k}|. The coefficient sum defining M_n bounds the total of these suprema. Taking half the L1 difference gives a one-cell TV bound M_n Var/4; replacing cells one at a time and using contraction/triangle inequality gives M_n Σ Var_i/4 ≤ M_n J/8. The cap n is fixed, but there is no cap on the number of source cells. No statistical noise assumption is used.

## Negative result: the same projection cannot extend uniformly to BOTH

Take N≥2 repeated cells with q0=1−1/N, q1=1−1/(10N), g=1/4, bracketed on each side by E(99/100). Each cell is strict. Set z=(99/100)². The COMMON cell pair factor is μ=1−13/(40N). The INDEPENDENT pair factor is

    g² q0 + (1−g)² q1 + 2g(1−g) = 1−19/(160N),

because roots assigned different arms cannot merge in that cell. Thus C_N=z(1−13/(40N))^N and I_N=z(1−19/(160N))^N are the two pair survivals. The above exact η_i formula gives η_i=O(1/N²), hence J_N=(1+η_i)^N−1→0. The COMMON-only theorem therefore makes this family arbitrarily close at all fixed finite arities to its COMMON ordinary projection.

For **every** equal-arm word with COMMON pair survival C', its INDEPENDENT pair survival I' satisfies 2I'−1−C'≤0. To see this, write its normalized INDEPENDENT pair factor as 1+2g_i(1−g_i)(1/q_i−1)≤(1+1/q_i)/2. For a,b≥1, ((1+a)/2)((1+b)/2)≤(1+ab)/2. Multiply these bounds over cells; the product of 1/q_i is at most 1/C' because of the ordinary clock. This proves the ceiling, even without restricting the number or order of cells.

But the exhibited unequal-arm family has

    lim (2 I_N−1−C_N) = 2z exp(−19/160)−1−z exp(−13/40)
                      ≥ 451111/32000000 > 0.

The rational lower bound uses exp(−x)≥1−x and exp(−x)≤1−x+x²/2 for x≥0. Thus it stays a fixed positive distance away from every equal-arm BOTH proxy, even if the latter is allowed to change its COMMON clock: putting ε=max(|I_N−I'|,|C_N−C'|) gives 3ε≥2 I_N−1−C_N. At matching C' the factor 3 improves to 2. No function tending to zero with J alone can bound this BOTH distance uniformly on the admitted class. The mechanism is accumulation of a first-order INDEPENDENT routing effect from many small biased unequal-arm cells, despite the COMMON Jensen defect shrinking quadratically per cell. In this family the weighted L1 mismatch sum Σ g_i(1−g_i)|q0_i−q1_i| stays positive.

This obstruction does not imply a failure of all possible BOTH stability theorems. A different proxy grammar, a new observable that bounds the accumulated drift, or a cell-count or routing-bias restriction may change the conclusion. It also does not alter exact-face v1–v3.

## Fixtures

Run `python3 -B g4-rh-certificate-v4/common_face.py` with the sibling v1 directory present. Four exact-arithmetic tests cover the Jensen identity, the COMMON count-kernel comparison on 36 unequal-arm triples of factors and entering arities up to four, seven increasingly long unequal-arm counterexamples with a fixed positive pair separation, and the rational lower bound on the asymptotic separation. The full labelled-forest result is from the hand argument, not the count fixtures. No formal verification or historical priority is claimed.
