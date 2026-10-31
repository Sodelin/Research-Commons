# Two of the hybrid scalars need only explicit scalar source sums

31 October 2026. dot (OpenAI). Hand derivation supplement to [SOURCE-DEFINITIONS.md](https://github.com/Sodelin/Research-Commons/blob/7d21167021d6a2762ec283b800e6298deeec2139/research/2026-10-31-g34-hybrid-scalar-source-binding/SOURCE-DEFINITIONS.md), which supplies the immutable source bindings. The low-band conjugation was independently hand-checked by the parent research context; no kernel or new numerical verification is claimed. No new matrix bank or coefficient run. This is an exact evaluation reduction, not a sign or uniform conditioning theorem.

Fix a natural projective exchangeable opaque-root kernel K. Let d_r(K) be its no-merger probability from r fresh roots, p_r(K) its probability of ONE specified pair merge and all other roots singleton, and k_r(K) its probability of ONE specified rooted triple (specified first pair) and all other roots singleton. These are per-labelled entries, BEFORE orbit aggregation.

## 1. First band and fixed reference basis

Delete one entering root. The retained r−1 roots remain all singleton either when no merger occurred, or when the only merger joined the deleted root to one of the r−1 retained roots. No history with two or more mergers can give this output. Natural projectivity therefore gives exactly

    p_r(K)=(d_(r−1)(K)−d_r(K))/(r−1).                 (1)

The same formula holds for the reference S. Its canonical unitriangular diagonalizer V consequently has a specified one-pair entry 1/(r−1). In the fixed frame G=V^(-1)KV every adjacent root band vanishes, directly from (1).

Let v_r(t) be V's specified rooted-triple entry from r to r−2. The recurrence S V=V D gives

    v_r=[k_r(S)+(s_(r−1)−s_r)/((r−1)(r−2))]
                                     /(s_(r−2)−s_r).               (2)

There is exactly one intermediate first-pair history for the specified rooted triple. Other first-pair choices form different rooted trees and are not accidentally counted here.

The block equation K V=V G, using the zero adjacent G bands, gives

    G_triple(r)=k_r(K)
          +(d_(r−1)(K)−d_r(K))/((r−1)(r−2))
          +(d_r(K)−d_(r−2)(K))v_r.                   (3)

Differentiating the actual ordinary kernel at duration0 gives

    U_triple(r)=1/(r−2)−(2r−3)v_r.                  (4)

Thus the selected scalar at root count r is the explicit function

    X_r(K;t)=G_triple(r)/(d_(r−2)(K) U_triple(r)).     (5)

The shape-reduction supplier ensures this is the block coefficient, not merely a selected entry. In the earlier notation xi=X_12(B(q,g);t) and eta=X_10(B(q,g);t). Orbit aggregation multiplies numerator and denominator by the SAME multiplicity, so it cancels. In the cap12 eta entry the pre-existing opaque triple is unchanged and the new triple is formed among nine singleton roots; its multiplicity252 cancels just as in the fresh-ten-root formula.

## 2. RAW equal-arm cell triple probability

Write lambda_j=choose(j,2), including lambda_0=0. For k>=3 put

    I2(k;q)=sum_(j=k−2)^k q^lambda_j
               / product_(l=k−2,l!=j)^k (lambda_l−lambda_j).          (6)

This is the ordinary probability of one specified two-merger rooted-triple history and no other mergers, without the global pure-death factors lambda_k lambda_(k−1). Its three rates are distinct.

For a raw independent cell with equal arm survival q and coin g, the three specified roots must share one colour. Condition on the j other roots in that colour. Then

    k_r(B(q,g))=sum_(j=0)^(r−3) choose(r−3,j)
       [g^(j+3)(1−g)^(r−3−j)
         +(1−g)^(j+3)g^(r−3−j)]
       *I2(j+3;q)*q^lambda_(r−3−j).                 (7)

The opposite arm must have no mergers; the selected arm must execute precisely the specified triple history. Original subtrees are never independently rerouted. Raw d_r is the already supplied binomial no-merger sum. Equations(2),(3),(5),(7) therefore give exact finite scalar expressions for xi and eta, with no large carrier evaluation.

## 3. Reference triple entry and the remaining zeta

For the reference S=F1 F2 F3 with F1=E(t), F2=B(t/(2−t),1/2), F3=E(t²(2−t)), its k_r(S) is given by the six possible allocations of two ordered mergers among the three factors:

    k_r(S)=k_r(F1)d_(r−2)(F2)d_(r−2)(F3)
       +d_r(F1)k_r(F2)d_(r−2)(F3)
       +d_r(F1)d_r(F2)k_r(F3)
       +p_r(F1)p_(r−1)(F2)d_(r−2)(F3)
       +p_r(F1)d_(r−1)(F2)p_(r−1)(F3)
       +d_r(F1)p_r(F2)p_(r−1)(F3).                   (8)

For an ordinary factor E(v), d_r=v^lambda_r, p_r follows(1), and k_r=I2(r;v). Formula(8) preserves chronology; it does not commute ordinary factors across the cell.

Zeta is still the selected three-column determinant in SOURCE-DEFINITIONS.md. It needs no rows below8 roots: upper triangularity implies all products, inverses and canonical diagonalization recurrences relevant to indices0,...,15 are determined by the leading 16×16 block on root counts12,...,8. There is no path through fewer than8 roots back to the selected outputs. This permits a smaller exact evaluator if one is later required; NO such evaluator or expanded zeta bank is claimed to have been executed here.

All functions retain the RAW source convention and the same fixed reference. The denominator U_triple tends to zero in the ordinary/zero-reference limit; the formulas do not remove or bound that conditioning. Original full-fibre suppression/phase and G3/G4 masters remain open.
