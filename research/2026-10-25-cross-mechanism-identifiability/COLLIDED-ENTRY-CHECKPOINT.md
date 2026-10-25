# Collided entry atoms: multiplicity is observable

Author: dot (OpenAI), 25 October 2026. Written component checkpoint awaiting review; bounded exact-rational controls executed. No full-master completion, formal verification or novelty claim. Assumptions and known-boundary restrictions are those of GENERIC-ENTRY-MIGRATION-IDENTIFICATION.md, except that repeated x_i=p_i lambda_i are now allowed.

## 1. A stronger observable family

For k>=2 let f_k(t) be the joint density of one specified ranked k-leaf binary merger chain, with first waiting time t and all subsequent waiting times taken to zero by right limits. These are density limits, not positive-probability simultaneous mergers. In the structured coalescent with k ordered lineages, write

    f_k(t)=alpha_k exp(K_k t) v_k,

where alpha_k=p tensor ... tensor p, K_k is the no-observed-coalescence killed generator, and

    v_k(s_1,...,s_k)=lambda_i^(k-1) if all s_j=i, and 0 otherwise.

Thus f_k(0)=a_k from the earlier star calculation. Put u=pQ, whose entries sum to zero. Then direct differentiation gives

    b_k=f'_k(0)
       = k sum_i u_i x_i^(k-1)
         - binom(k,2) sum_i x_i^k.

Proof: under the migration-only product generator M_k, the derivative at zero of alpha_k exp(M_k t) is the sum over coordinates replacing p by pQ. Its evaluation on v_k is k sum_i u_i p_i^(k-1)lambda_i^(k-1). On the pure state i^k, the killing hazard is binom(k,2)lambda_i, so alpha_k D_k v_k=binom(k,2)sum_i p_i^k lambda_i^k. Subtraction proves the formula. This uses independent boundary routing, not stationary p or reversibility. Migration rates are arbitrary finite rates.

## 2. Collision multiplicities, not just combined weights

The a_k recover the finite positive x-support and its combined weights. For each distinct support value x, define U_x=sum_(i:x_i=x) u_i and m_x=#{i:x_i=x}. Then

    b_k/k = sum_x [U_x - (k-1)m_x x/2] x^(k-1).

Distinct positive x give linearly independent exponential-polynomial sequences x^n and n x^n. Therefore the b_k determine each U_x and each m_x. One may use a finite confluent Vandermonde system after the x-support has been recovered. This is classical linear algebra applied to these actual genealogy coefficients, not a new general moment theorem.

In particular, if every x_i equals one x, then sum_i u_i=0 and

    b_k = -binom(k,2) d x^k.

So the number d of entry demes is visible even with arbitrary migration. The initial single-star moment collision cannot be promoted to an exact genealogy collision.

This still does not identify the individual p_i and lambda_i within a collided x-group. Nor does it extract separately addressable hidden states or prove the required tensor-compatible maps.

## 3. Higher-order route: candidate, not yet a general proof

For fixed derivative order r, consider f_k^(r)(0)=alpha_k K_k^r v_k as k varies. A candidate decomposition, for k>r, is a finite sum of x_i^(k-1) times polynomials in k of degree at most 2r. The proposed top-degree coefficient at support x is

    (-1)^r / 2^r * sum_(i:x_i=x) p_i lambda_i^r.

The heuristic is structural: every coalescence-killing factor is quadratic in lineage counts, while finite migration acts one lineage at a time and contributes lower-degree terms. The pure killing word supplies the displayed coefficient. A complete proof must control the multinomial initial weights and all noncommuting migration/killing words; naive operator-degree counting alone is insufficient because summing over near-pure starting configurations can introduce additional factors of k.

If proved, these coefficients would identify the finite positive rate measure within each x-group, and thus recover the multiset of (p_i,lambda_i), including multiplicities. It would still not automatically identify individual equal-parameter demes or their migration rates; an observable joint-preparation/partition step would remain.

The exact-rational check below supports this route but does not prove the candidate for arbitrary r, k, d or rates.

## 4. Executed controls

check_entry_coefficients.py uses only Python exact Fraction arithmetic. With three demes, p=(1/2,1/3,1/6), and a nonreversible finite migration generator with rows (-3,1,2), (3,-4,1), (2,2,-4), it checked:

- a_k and b_k formulas for k=2,...,6 with distinct x (rates 2,6,18) and fully collided x=1 (rates 2,3,6).
- All six directed three-block coefficient identities q_(j,i)lambda_i^2.
- The proposed higher-derivative leading coefficient at r=1,2,3 in the fully collided case, using exact finite differences in k. Values were -3/2, 11/4, -49/8.

The log is entry-coefficient-control.json. These are bounded algebra controls, not empirical model recovery, a uniform proof or a sample-complexity result. The benchmark's sequence-level simulation and estimation remain unexecuted.
