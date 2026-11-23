# G4 v2: quantitative stability of the one-fair-bigon boundary

This extends the sibling v1 hand proof and does not change it. Same hypotheses: original same-source BOTH access and admitted observation-to-private-kernel adapter, strict finite matched private E/B words, and the ordinary COMMON face identified by the exact equality b3_C = C³ with C=b2_C. In particular we do not certify closeness for an approximately ordinary COMMON face. The result is a uniform-in-word-length estimate for each fixed finite entering arity, not an all-arity bound, a noisy-observation theorem, or general G4.

## Quantitative theorem

Write

    U = b2_I/C − 1,  V = b3_I/C³ − 1,  Δ = V − 3U − 3U².

Suppose U>0. For every cell put h_i=g_i(1−g_i), u_i=2h_i(1/q_i−1)>0, and d_i=3u_i²(1/(4h_i)−1). Ordinary factors contribute no excess. Then for any partition of the cells into two groups with excesses A and B (one plus the excess equals the product of 1+u_i in that group),

    Δ ≥ 3AB(U+AB) + Σ d_i
      ≥ 3AB(U+AB) + 12 Σ u_i²(g_i−1/2)².          (1)

Reason: the normalized triple factor is P(u_i)+d_i, P(u)=1+3u+3u². Expanding its product gives at least the product of P(u_i) plus Σd_i, since P(u_i)≥1. The v1 supermultiplicative identity gives product P(u_i) ≥ P(A)P(B)=P(U)+3AB(U+AB), using U=A+B+AB. Also d_i=3u_i²(g_i−1/2)²/h_i and h_i≤1/4. These inequalities allow explicit additive allocation of the gap between splitting and bias; they do not penalize a nearly unused coin heavily unless its pair-excess contribution is appreciable.

Let R=U/[4(1+U)]. If Δ<3UR², at least one cell has excess at least R. Otherwise take cells in their original order until the first group crosses R. The aggregate excess A of that group is at least R and less than 2R+R²≤9U/16; the other group has B=(U−A)/(1+A)≥(7U/16)/(1+U)>R. This contradicts (1). Choose a largest u_i=m and let b be the aggregate excess of all remaining cells. Then from the dominant/tail partition,

    b ≤ b_max := Δ/(3UR);
    m = (U−b)/(1+b) ≥ m_min := max{R,(U−b_max)/(1+b_max)};
    (g_dom−1/2)² ≤ Δ/(12 m_min²).                (2)

Here b_max<R and the largest cell is unique in that regime: any other cell's excess is at most b. In particular for fixed U>0, gap tending to zero forces the tail excess and dominant bias to tend to zero. A nonzero gap does **not** tell you that there are fewer than some fixed number of cells unless each cell is independently known to contribute a positive minimum. Under a minimum excess τ>0 for nondominant cells, the explicit bound (1+τ)^(number of nondominant cells) ≤ 1+b_max follows.

## Full labelled-forest stability, not merely diagonal stability

Let W* be the word formed from the physical rival W by replacing each nondominant bigon B(q,q,g) with E(q) in the same position, and changing the dominant coin to 1/2 without changing its q or position. W* has the same entire COMMON law and merges ordinary factors on either side into a one-fair-cell word. Its position is not inferred from the four gap inputs; the v1 chronology formula applies at exact equality. We have, for any ordered entering labelled forest with at most n roots, the INDEPENDENT output-kernel total variation bound

    TV(W,W*) ≤ min{1, choose(n,2) b + n|g_dom−1/2|}.                  (3)

To see this, first compare B(q,q,g) to E(q). Draw the ordinary comparison's initial root colors using the same independent arm coins. Use the same pair clocks for within-arm mergers. While forests agree, only an ordinary cross-color merger can separate the two processes. If k of r≤n incoming roots were given the first color, the pre-disagreement cross-pair rate is at most k(r−k) because within-color merges only lower color counts. Both arms have the same time t=−log q. The probability of disagreement is at most t E[k(r−k)] = tr(r−1)h. Since −log q ≤ 1/q−1, this is at most choose(n,2)u. For the dominant comparison, couple independent fair and biased coins with a shared uniform per root, so the chance they disagree anywhere is at most n|g_dom−1/2|. Compose the couplings sequentially; the number of roots never increases, and the union bound plus Σ_tail u_i≤b gives (3). If times are retained as part of the forest state the common clocks also couple the within-cell merge times. Replacing nondominant cells need not erase their ordinary clock time, which may be large even when their deviation from ordinary behavior is tiny.

Combining (2)–(3) gives a bound entirely in observable quantities: substitute b_max and sqrt(Δ/12)/m_min in (3). This is proximity to *some* one-fair-cell representative. By contraction, a fixed postprocessing of the private forest retains this bound; extending it through arbitrary testers would require controlling entering arity and every use of the private interface. It cannot be interpreted as a uniform bound over all sizes or as exact equivalence at a positive gap.

## Exact fixtures

Run `python3 -B g4-rh-certificate-v2/gap_certificate.py` from the directory containing both v1 and v2. It reuses v1's rational root-count kernel simulator. Five tests exercise the zero-gap case, 50 small cells that cannot masquerade as the near-equality regime, a rare long-clock cell and a slightly biased dominant cell, exact group and bias inequalities, and invalid scope / inadmissible data. The TV fixture is for root counts only; the uniform labelled-forest assertion comes from the hand coupling. No publication or formal proof verification is claimed.
