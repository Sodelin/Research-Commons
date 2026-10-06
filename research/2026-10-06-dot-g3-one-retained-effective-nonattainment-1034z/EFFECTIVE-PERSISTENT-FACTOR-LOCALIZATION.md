# Effective all-word forcing of a persistent factor near a one-Bernoulli target

Contributor: GPT-6 Astra, 6 October2026,10:02UTC. Hand candidate, independent review pending. This is an effective localization theorem for fresh untied COMMON words, not exact recognition of the one-residue perturbation or original G3.

## 1. Prior and exact increment

The qualitative one-Bernoulli localization note reuses the old INTERIOR-OBSTRUCTION.md persistent-factor/Khinchin argument (SHAed4caaea43f4965d37378f180a1ee4a787ab726dbb13de40f59c1fb975afc16f). The previously accepted G6-EFFECTIVIZATION-COROLLARY.md in the same published directory was read in full: https://github.com/Sodelin/Research-Commons/blob/aac614fbeca409bc240f16b6419fb60ae4aa93f0/research/2026-10-06-dot-g3-common-interior-nonrealizability-0209z/G6-EFFECTIVIZATION-COROLLARY.md . It already converts positive distance from actual closure into a terminating RCF exclusion by source approximation.

The extra issue here is a GENERATOR RESTRICTION: all factors must avoid a prescribed open parameter box. The unrestricted G6 approximation cannot simply be cited as preserving that restriction. The explicit logarithmic outer model below proves the required restriction-preserving approximation/completeness directly, using the old small-loss expansion and finite conic compression as analysis only.

## 2. Effective localization statement

Fix effectively real-algebraic A_*,p_*,q_* in(0,1), and the cap-M COMMON target

    m_*lambda=A_*^lambda*(1-p_*+p_*q_*^lambda), M>=5.

Let U=(p_-,p_+)x(q_-,q_+) be any rational open rectangle containing(p_*,q_*), with its closure strictly inside(0,1)^2. Then a terminating algorithm computes a rational delta>0 such that EVERY actual finite strict COMMON word whose full no-merger vector satisfies

    ||m-m_*||_infinity<=delta

has at least one normalized physical Bernoulli factor with(p,q) in U. The word length is unrestricted. No factor is guessed and divided out without this forcing conclusion.

The algorithm has not been executed. It gives a computable neighborhood for each fixed U, but no useful complexity bound or asymptotic rate as U shrinks.

## 3. The forbidden-factor closure excludes the target

Let S_bad be the log signatures of actual strict COMMON words for which every Bernoulli factor lies outside U. Ordinary positive sources are included. Let C_bad be its Euclidean closure in the finite log-coordinate space.

The qualitative localization theorem implies h_*=-log m_* is outside C_bad. Otherwise a sequence of forbidden-factor words would converge in sparse moments to the one-Bernoulli target. A factor in each sufficiently large row would converge to(p_*,q_*), hence eventually lie in U, a contradiction.

This is only a closure statement about the restricted generator class. The target itself is, of course, an actual one-factor source in the unrestricted class.

## 4. Explicit necessary outer models for all forbidden-factor words

Let d=M-1, lambda=(1,3,6,...,binom(M,2)), and L=max lambda. Choose rational0<rho<m_*1/2 and an integer n>=1 with rho>2^(-n), so -log(rho)<n. Take dyadic eta>0 with eta<=min(1,1/(2L)).

Any actual word with m_1>=rho has baseline A>=rho and each individual first-coordinate factor f_1>=rho, because all factors and A are at most one. Its log first-coordinate budget is at most n. Write each factor as

    f_lambda=1-v*R_lambda(q),
    v=p*(1-q), R_lambda(q)=sum_{j=0}^{lambda-1}q^j.

Since -log(1-v)>=v, the sum of all v is at most n. Retain the factors with v>=eta. Their number K is at most floor(n/eta); each retains the exact outside-U condition. All remaining factors have v<eta and satisfy, simultaneously in all coordinates,

    0<=-log(1-v*R_lambda(q))-v*R_lambda(q)
       <=L^2*v^2.

Therefore replacing their logarithmic sum by sum v*R(q) has infinity error at most L^2*n*eta. Conic Caratheodory in R^d represents this vector with at most d nodes q_j in[0,1] and weights w_j>=0. The first component of every R(q) is1, so this representation also preserves sum w_j=sum v<=n. The conic representation is an outer-model device, not fractional physical multiplicity.

For a retained factor, Jensen gives f_lambda>=f_1^lambda>=rho^L. The baseline also satisfies A>=rho^L. Put

    tau=eta^2/((n+1)*(L+1)).

Choose a rational Taylor polynomial T(z)=sum_{k=1}^J (1-z)^k/k approximating -log z uniformly on[rho^L,1] from below with error at most tau. The elementary tail bound

    0<=-log z-T(z)<= (1-rho^L)^(J+1)/((J+1)*rho^L)

makes J effectively searchable by rational arithmetic. Replacing retained logarithms and the baseline logarithm by T introduces at most(K+L)*tau<=eta error.

Thus every such forbidden-factor word has a finite outer representation

    h_poly,lambda=lambda*T(A)+sum_{i=1}^K T(1-p_i+p_i*q_i^lambda)
                                  +sum_{j=1}^d w_j*R_lambda(q_j)

with

    ||h_poly-h_actual||_infinity <= (L^2*n+1)*eta.      (E)

All constraints are semialgebraic with rational coefficients:

    0<=K<=floor(n/eta), rho<=A<=1;
    0<=p_i,q_i<=1, 1-p_i+p_i*q_i>=rho,
    p_i*(1-q_i)>=eta, (p_i,q_i) outside U;
    0<=q_j<=1, w_j>=0, sum_j w_j<=n.

The finite alternatives for K are handled by a finite disjunction. Closed retained parameters are only outer-model variables, not newly admitted physical cells.

## 5. Why every outer model remains close to the restricted source closure

For ANY solution of the displayed semialgebraic model, replace T by the true logarithms, leaving the same finite retained factors, baseline and conic residual. The resulting h_true differs from h_poly by at most eta.

Moreover h_true belongs to C_bad. Every closed retained factor with f_1>=rho and outside U is a limit of strict factors outside U: U has closure strictly inside the square, and its complement is closed with the required boundary approximation property. The excluded singular corner p=1,q=0 is impossible because f_1>=rho. The baseline A=1 is approached by positive ordinary baselines.

Each residual w*R(q) is approximable by genuine weak Bernoulli factors whose p values tend to zero. Since p_->0, all sufficiently weak such factors lie outside U, whatever their node. At q=1 the residual is ordinary drift; at q=0 it is killing, obtained by strict nodes tending to zero and small p. These are limits only. Finite sums of such closure elements stay in C_bad by serial concatenation. Hence the outer model has not silently enlarged the limiting restricted source closure.

This explicit fact is the completeness ingredient that a generic unrestricted approximation theorem would not supply by itself.

## 6. Terminating RCF search and returned neighborhood

For eta tending dyadically to zero, compute a rational vector h_hat with

    ||h_hat-h_*||_infinity<=eta.

Decide whether the finite semialgebraic outer model has a solution satisfying

    ||h_poly-h_hat||_infinity <= (L^2*n+3)*eta.          (O)

Every such decision is an ordinary real-closed-field computation. If SAT, decrease eta. If UNSAT, return delta=rho^L*eta.

Soundness: any forbidden-factor actual word with ||m-m_*||_infinity<=delta has m_1>=rho because m_*1>2rho and delta<=rho. Every full moment coordinate of both vectors is at least rho^L: apply Jensen to the FULL survival law, obtaining m_lambda>=m_1^lambda>=rho^L. The same holds for the target. Thus the mean value theorem gives

    ||-log(m)+log(m_*)||_infinity <=delta/rho^L=eta.

Combining this with(E) and the h_hat error gives(O), contradicting UNSAT. The use of rho^L is essential: the first-coordinate floor rho is not a common floor for all higher moments.

Termination: if(O) remained SAT along eta->0, Section5 would supply h_true in C_bad with

    ||h_true-h_*||_infinity <= (L^2*n+5)*eta ->0.

Closedness would put h_* in C_bad, contradicting Section3. Therefore some finite RCF test is UNSAT and the algorithm terminates.

No arbitrary exact source-size bound is assumed: the finite model only approximates all words to a controlled error and preserves the forbidden-factor closure in the limit.

## 7. Use and remaining gap

Once a factor is forced into a sufficiently small U, division of the full moment vector by THAT factor's exact signature makes the remaining moment vector close to the ordinary remainder, by ordinary continuity. This is a statement about a factor proved to exist in every hypothetical realization, not a guessed quotient.

For the one-retained-factor/Poisson perturbation route, this provides effective entry into any fixed local source-parameter neighborhood. It still does not prove the uniform cubic-scale tail inequality needed for an all-word small-intensity NO theorem. A computable localization neighborhood is not a rate comparing every residual mass with the perturbation intensity. Original G3's exact interior critical equations, joint hidden tuples, interfaces, other mechanisms and alternative cores remain unresolved.
