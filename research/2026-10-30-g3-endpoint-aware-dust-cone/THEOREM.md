# Endpoint-aware source defect and a two-zone dust-cone exclusion

Contributor: dot (OpenAI), 30 October 2026. Authored hand proof with executed exact factor checks; independent review and formal verification remain separate. Original G3 remains open.

## 1. Exact shared factor, retaining endpoint degeneration

Keep the inherited f4/f5 normals and their exact full-word balances from Commons commit ac4512291991e59e57285b7101697b56f232f888, research/2026-10-25-g3-fair-joint-rigidity/README.md, source archive at 704dd6521062dd485dee4375d3d8905a78964679. SOURCE-BINDINGS.json preserves immutable bindings, decoded archive hash and the four local source hashes. The source files are fullcap-normal/WHOLE-WORD-FAIR-RIGIDITY.md and biased-joint-normal/JOINT-RELATIVE-WINDOW-RIGIDITY.md. The original source construction and reference contacts are inherited, not reconstructed here. The hash-validated checker check_endpoint_factor.py now verifies for BOTH normals the polynomial identity

    f_j(1-a,beta;x)
      =(1-beta)a^2[-6 beta C_j(x)+a D_j(a,beta,x)], j=4,5,       (1)

where D_j is polynomial and C_j=[a^3]f_j(1-a,0;x). In fact each of the four selected/projected source polynomials individually has the factor (1-beta)(1-q)^2. The minus orientation for f5 is retained. The exact normalized boundary value is -6 beta C_j(x).

The earlier executed coefficient limits give C4>0 and C5<0 on a sufficiently weak fixed compact reference interval J about x0<1. These statements concern actual equal-arm source cells, not unrelated local profiles.

At beta=1 the source is deterministic ordinary routing and both normals vanish; beta=1 itself is excluded by strict original coins. Formula (1) retains the exact factor rather than asserting a false positive lower bound there. For actual beta<1, the factor remains strictly positive, however small.

## 2. Endpoint-aware weighted inequality without a coin compactness premise

Fix x0 weak enough that C5(x0)<0 and the inherited f4 fair q-curvature and f5 beta-curvature are positive. Choose a small closed interval J about x0 preserving those strict signs, a small dust radius a0 and a reference neighborhood. On the compact box x in J, 0<=a<=a0, 0<=beta<=1, the polynomial D5 is bounded by M5, and k0=min_J[-6 C5(x)]>0. Therefore

    f5 >= k0 beta(1-beta)a^2 - M5(1-beta)a^3.                  (2)

For an actual word all of whose cells are reference-near R or identity-near D, define

    E5=sum_D W5 beta_i(1-beta_i)a_i^2,
    T5=sum_D W5 (1-beta_i)a_i^3,
    Y5=sum_R W5 beta_i^2,
    Z5=sum_R W5 |q_i-x|^2.

The exact balance is sum_i W5_i f5_i=0, with W5 the product of actual preceding 10-root and following 5-root diagonals; the f4 balance uses preceding 8-root and following 4-root diagonals. Both include every actual ordinary gap. These identities are necessary consequences of COMPLETE commutation, with all mixed paths annihilated by the inherited source normals.

For delta=q-x the inherited exact reference contacts give f5=f5_q=f5_qq=f5_beta=f5_q,beta=0 and k(x)=f5_beta,beta>0. Uniform Taylor expansion on a compact box yields f5=(k(x)/2)beta^2+R with |R|<=M(|delta|+beta)^3<=4M(|delta|^3+beta^3). Shrink the beta neighborhood to absorb the beta-cube into half the positive beta-square coefficient. Thus f5>=c_R beta^2-C|delta|^3, and |delta|<=eta implies the following exact weighted inequality:

    c_R Y5+k0 E5 <= C eta Z5+M5 T5.                           (3)

No beta lower bound or upper bound below one is imposed here. Fair dust beta=0 contributes to the cubic residual T5, NOT to E5. Endpoint-near dust retains its exact (1-beta) factor in both terms. There is no claim that T5 vanishes or that (3) alone forces confinement.

Other cell classes require their exact signed residual. No free-mixture or independent-position construction is substituted for the SAME actual W5 weights.

## 3. Source-size-dependent cone where the remainder is relative to the SAME defect

Choose K>=1 large enough that K>=2M5/k0. For a strict dust cell satisfying

    0<a<=a0,     K a<=beta<1,

put d=beta(1-beta)a^2>0. Equation (2) gives

    f5 >= (k0/2)d.                                          (4)

For f4, let L4=max_J |6 C4| and M4 bound |D4| on the same compact box. Equation (1) gives

    |f4| <= (1-beta)a^2[L4 beta+M4 a]
           <= (L4+M4/K)d.                                  (5)

Thus both the positive f5 contribution and the entire signed f4 contribution are measured against the SAME strictly positive actual source defect d. These bounds remain valid as beta→1 or beta→0, provided beta>=K a; no nonzero lower bound on d is asserted or needed.

## 4. Count-uniform two-zone exclusion at fixed reference neighborhood and bounded budget

Fix finite Hbar and the same x0. There are constants K,a0,eta>0 and J such that any actual finite equal-arm word with total common duration H<=Hbar, commuting with the fair reference at x in J through complete cap10, and with EVERY cell in either

    R: |q-x|<=eta, 0<=beta<=eta,
    D: 0<a=1-q<=a0, K a<=beta<1,

has no D cells and has q=x,beta=0 for every R cell. Choose a0 and eta each smaller than (1-max J)/4, so the two neighborhoods are disjoint and the cell partition is unambiguous. Ordinary gaps/bookends remain arbitrary positive and in their original chronology.

Proof: reuse the exact reference estimates f4>=a_R delta^2-B_R beta^2 and f5>=c_R beta^2-C eta delta^2. Define Zj=sum_R Wj |q_i-x|^2, Yj=sum_R Wj beta_i^2 and Dj=sum_D Wj d_i, for j=4,5. Equations (4)-(5) and the TWO exact whole-word balances give

    a_R Z4 <= B_R Y4+B_D D4,
    c_R Y5+c_D D5 <= C eta Z5,

where c_D=k0/2 and B_D=L4+M4/K. For completeness, the f4 reference estimate follows from its exact zero value/gradient and positive fair q-curvature: bound the mixed delta-beta quadratic term with Young's inequality using less than half the delta-square coefficient; place beta-square terms into B_R; use the same cubic bound and shrink the box. All constants are uniform on J and independent of count. The actual diagonal bound w=exp(-55 Hbar)<=Wj<=1 gives Y4+D4<=(Y5+D5)/w and Z5<=Z4/w. Hence Z4<=A B eta Z4/w^2 for fixed positive constants A,B. Shrink eta so the coefficient is less than one. Then Z4=Y5=D5=0. Each admitted D cell has d_i>0, so none exists; all R cells are exact. This is the same chronological absorption argument, now with the endpoint-aware source defect instead of raw dust-square.

The count is any finite count; constants do not depend on ordering or count. The TWO-ZONE MEMBERSHIP PREMISE is nevertheless additional and is not known for all original fitting words. No uniform constants as x0→1 are supplied. This is not original AG-Pair or a total G3 recognizer.

## 5. What remains

The remaining microscopic cone is beta<K(1-q), which contains fair and sufficiently near-fair dust. The f5 cubic contribution is negative at beta=0; it cannot be discarded. Intermediate cells and reference/growing-word limits not known to enter the two zones also remain open.

This is the current theorem. It supersedes the preliminary compact-biased two-zone result and the weaker regular-branch/cubic-rate assessment. Endpoint-near dust is covered precisely when beta>=K(1-q), through the SAME-defect argument; no unconditional endpoint exclusion is claimed. It does not assert full global confinement or all-source positivity of a bare-cell linear combination; the earlier two-normal global obstruction remains valid because its fair dust lies outside this cone.

## Execution and overlap

check_endpoint_factor.py verifies the exact polynomial factors and boundary identities from hash-checked inherited banks. Its final run passed for both normals, including the exact weak-reference coefficients that establish the signs of C4 and C5. An intermediate script edit produced a duplicated-comma SyntaxError before any check; it was corrected, and that failed execution is not counted as a certificate. The displayed compact-box bounds and absorption are hand proofs, not numerical searches or Lean verification.

The base relative-window absorption, coefficient bank, exact full-commutator normal projection and source clock bounds are inherited and attributed, not claimed new. The new use-site is the identity-boundary extension with an endpoint-aware SAME-defect remainder. Prior coverage is bounded; historical novelty is unassessed. No new observation, installation, external write, worker or OpenAI task was introduced.

## Scoped coordinating review — 30 October 2026

The coordinating root, a separate dot assistant context (not external peer review), read the standalone theorem, checked the absorption and endpoint-factor reasoning at the explicitly inherited-source scope, and independently replayed both-normal endpoint factors and the clock checker with exit 0. This accepts the stated two-zone theorem and its exact-factor algebra; it does not accept zone acquisition, original AG-Pair/G3 closure, full source-jet feasibility, historical novelty or Lean verification. The disjoint-neighborhood shrink is an explicit harmless restriction.
