# A weighted bias budget controls the abstract pair comparison

This is an exact comparison of two scalar products in the model of [G4 v4](g4-rh-certificate-v4/README.md), not a full G4, kernel or source-recognition result. No higher arity or application assumption is made.

For a finite ordered list of triples 0<a_i,b_i,g_i<1, write w_i=g_i(1−g_i), μ_i=g_i a_i+(1−g_i)b_i. Consider the two local scalar factors
    p_i=g_i²a_i+(1−g_i)²b_i+2w_i,
    q_i=(1−2w_i)μ_i+2w_i.
The common pair factor μ_i is the same before and after replacing both arms by μ_i. Independently of word length,
    |∏p_i−∏q_i| ≤ min(1, sqrt(J B/2)),
where
    1+J=∏[(g_i a_i³+(1−g_i)b_i³)/μ_i³],  B=Σ w_i(2g_i−1)².

Indeed p_i−q_i=w_i(2g_i−1)(a_i−b_i) exactly. Both factors lie in [0,1], so product telescoping bounds the full difference by Σ|p_i−q_i|. The Jensen identity in v4 gives Σ w_i(a_i−b_i)²/μ_i²≤J/2. Factor each absolute difference into sqrt(w_i)|a_i−b_i|/μ_i times sqrt(w_i)|2g_i−1|μ_i, then use Cauchy and μ_i≤1. A shared ordinary scalar prefactor in [0,1] cannot increase the bound.

Thus balanced g_i=1/2 gives exact pair agreement regardless of the per-cell variance; this does not extend automatically to other arities. A bounded bias budget B is enough for uniform pair convergence as J tends to zero, even if the number of balanced cells diverges. By contrast, the repeating g=1/4 example in v4 has B=3N/64, so its counterexample is consistent with this bound. A small nonzero J alone is insufficient on unbounded budgets.

Exact replay: python 2026-11-27-g4-abstract-pair-bias-budget.py. It checks 800 synthetic scalar words, an exactly balanced case with positive J, an unequal-arm biased case and four growing-budget examples. This is a hand inequality with rational regression tests, not Lean.
