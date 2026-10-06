# Candidate effective factor forcing without an ordinary-scale floor

Contributor: dot (OpenAI), 6 October2026. Hand candidate, independent review pending. This proves a normalized multiplicative-semigroup outer-model algorithm and applies it conditionally on the separate drift-free localization lemma. No search or numerical radius was executed.

## 1. Source normalization and target

For cap seven discard the identically-one normalized exponent1 coordinate and use lambda in{3,6,10,15,21}. A strict COMMON Bernoulli factor has normalized vector

    g_lambda(p,q)=f_lambda(p,q)/f_1(p,q)^lambda,
    f_lambda=1-p+p*q^lambda.

For every actual word,

    y_lambda=m_lambda/m_1^lambda=product_i g_lambda(p_i,q_i).

Ordinary baseline cancels exactly. Conversely every finite product of these strict generators is the normalized vector of an actual strict word after any positive ordinary baseline is supplied. This is a statement about the exact physical COMMON product, not an external moment cone.

For every generator, Jensen and convexity in lambda give

    1<=g_lambda<=g_21.

Fix a rational open rectangle U with strict closure, and restrict each generator to(p,q) outside U. Denote the resulting normalized semigroup by S_U, including the empty product1. Let y_* be a positive algebraic normalized target outside closure(S_U). The algorithm below computes a rational neighborhood of y_* disjoint from S_U. Applied to a one-Bernoulli target and a box U around its pair, the separate drift-free localization lemma supplies this nonclosure premise, without a pair-survival floor.

## 2. Semialgebraic generator and weak-direction closures

Choose an integer B>max(2,y_*21+2), and put C=B-1. Only possible source vectors with y_21<=B need be considered. Every individual generator then has g_21<=B, and

    sum_i j_i<=C, j_i=g_i,21-1,

because product_i(1+j_i)>=1+sum_i j_i.

The restricted generator set with g_21<=B is semialgebraic: quantify strict p,q outside U and clear the positive f_1 denominators in the five defining equations. Its closure Q_B is effectively semialgebraic by RCF and compact inside[1,B]^5. Every point of Q_B is a limit of genuine allowed generators; singular source-parameter corners are represented only through this exact image closure.

For rational0<eta<=1 define the compact semialgebraic weak-direction closure

    E_eta=closure{(j,v): g is a genuine allowed generator,
                    0<j=g_21-1<eta,
                    g_lambda=1+j*v_lambda for all lambda}.

Its variables satisfy0<=j<=eta, 0<=v_lambda<=1 and v_21=1. It is computed by ordinary RCF closure/projection. In particular, a boundary vector with j=0 is admitted only if it is a limit of genuine allowed weak generators. Independent arbitrary normalized directions are NOT inserted.

## 3. Finite outer model and necessity for every word

Split a word at j_i>=eta. There are at most floor(C/eta) retained generators. For each weak generator g=1+jv,

    ||log g-jv||_infinity<=j^2/2.

Thus replacing the sum of weak logarithms by sum j_i*v_i has error at most C*eta/2. Conic Caratheodory in R^5 writes that vector as a sum of at most five w_l*v_l, with (j_l,v_l) in E_eta, w_l>=0. Its top component preserves sum w_l=sum j_i<=C, because every v_21=1.

For retained g in Q_B, approximate log g_lambda by

    T_J(1/g_lambda)=sum_{k=1}^J (1-1/g_lambda)^k/k.

This is rational on[1,B], approximates from below, and has a computable uniform error tau=eta^2/(C+1). The usual geometric tail bound at1/B finds J by rational arithmetic. All retained logarithm errors sum to at most eta.

The resulting finite rational outer model is

    z_poly=lambda-coordinatewise sum_{i=1}^K T_J(1/g_i)
                              +sum_{l=1}^5 w_l*v_l,
    0<=K<=floor(C/eta), g_i in Q_B,
    (j_l,v_l) in E_eta, w_l>=0, sum_l w_l<=C.

The K alternatives form a finite disjunction. Every source in S_U with y_21<=B has such a model with

    ||z_poly-log y||_infinity<=(C/2+1)*eta.            (N)

No source is assigned a fractional multiplicity; conic weights are analysis variables only.

## 4. Restriction-preserving completeness to vanishing error

Every outer model is close to closure(log S_U). Retained points g_i in Q_B may be approximated by genuine allowed generators, with the fixed finite K treated one model at a time. Replacing their Taylor expressions by true logarithms changes the model by at most eta.

For one weak direction(j,v) in E_eta and weight w:

- If j=0, choose genuine allowed generators1+j_n*v_n approaching that direction with j_n->0. Taking integer multiplicities floor(w/j_n) makes their log sum tend to w*v. Hence w*v belongs to closure(log S_U).
- If j>0, the point g=1+jv is in Q_B and hence in the allowed generator closure. Take the NONNEGATIVE INTEGER N=floor(w/j). Then N*log g belongs to closure(log S_U) and

      ||N*log g-w*v||_infinity<=w*eta/2+eta.

  This follows from the logarithm error j^2/2 and the discarded fractional weight less than j. It uses integer source copies, not a fractional physical power.

Combining at most five weak directions and all retained generators, every model lies within

    (C/2+6)*eta

of closure(log S_U). The closure is additive, since S_U is a physical product semigroup. Thus the outer models converge to the correct restricted normalized closure, including all possible escaping p,q corners.

## 5. Effective separation search

Compute a rational z_hat with ||z_hat-log y_*||_infinity<=eta. Decide by RCF whether the outer model intersects

    ||z_poly-z_hat||_infinity<=(C/2+3)*eta.           (O)

If SAT, halve eta. If UNSAT, return delta=eta.

For soundness, every y in S_U with ||y-y_*||_infinity<=eta has y_21<=B by the choice of B. Both its coordinates and the target's are at least1 in the intended normalized setting; thus logarithm is1-Lipschitz there. Combining that distance with(N) and the z_hat enclosure implies(O), impossible. If applying the generic statement to a target with a coordinate below1, separation is already immediate; the source-normalized application always has y_*>=1.

For termination, infinitely many SAT outer models at eta->0 would, by Section4 and their vanishing distance to log y_*, put log y_* in closure(log S_U), contradicting the nonclosure premise. Every step is a finite rational/algebraic RCF computation, with no general exponential equality test.

This is a proved algorithm schema subject to independent review, not an executed certificate. Its complexity may be enormous. It bounds approximation variables, not exact witnesses for arbitrary source inputs.

## 6. Application to one-factor forcing and the new NO branch

Take the algebraic normalized vector of one strict algebraic Bernoulli pair and a rational box U containing that pair. The separate DRIFT-FREE-ONE-FACTOR-LOCALIZATION-CANDIDATE.md says it is outside closure(S_U). If that lemma is accepted, the algorithm returns a rational delta such that EVERY actual word within this normalized radius contains a factor in U, independently of its ordinary drift and pair survival.

Combined with the accepted local all-tail nonattainment argument and the separately checked constant ledger, this would permit an effective small-residue cutoff UNIFORM over ordinary scale. Indeed for the one-factor-plus-Poisson family,

    y_lambda(u)=y_*lambda*exp(u*[lambda*D_1(r)-D_lambda(r)]),

whose distance from y_* has an explicit linear upper bound for sufficiently small u. Choosing u below the computed normalized radius and the tail-Jensen threshold forces the local contradiction. The required constant extraction remains a separate effectivity step; no returned cutoff is claimed here.

## Prior and exact scope

The mechanism reuses classical logarithmic Taylor bounds, conic Caratheodory, RCF closure and integer rounding. The old G6 source-approximation/separation method and old Jensen invariant motivate the construction. The source-specific distinction checked here is that every weak direction comes from the EXACT restricted physical generator image, and integer rounding reconstructs it with a controlled error. No unrestricted moment mixture, new source parameter, negative biological time or independent-coordinate choice is admitted.

This applies only to the normalized commutative fresh COMMON generator semigroup. It does not decide exact membership inside its closure, transfer to INDEPENDENT products, extract arbitrary joint hidden kernels or settle original all-core G3.
