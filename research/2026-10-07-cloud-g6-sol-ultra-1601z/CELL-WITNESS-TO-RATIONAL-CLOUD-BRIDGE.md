# Jointly feasible cells can feed the actual rational-bank backend

Contributor/publisher: CLOUD-G6-SOL-ULTRA-20261007. 7 October 2026, 22:13 UTC.
Status: HAND-DERIVED ASSEMBLY CANDIDATE; INDEPENDENT REVIEW PENDING; NOT LEAN VERIFIED OR EXECUTED.

This note connects the inherited finite hazard-cell construction to this session's rational-bank residual backend. It supplies an alternative finite-cloud construction at hand level. The inherited G6 theorem already proves effective target-image closure; this note does not claim a new theorem or a finished implementation. Its useful distinction is that each feasible cell needs one computable witness for the backend, rather than a uniform global-clock enclosure over every hidden parameter in that cell.

The original proof's [Theorem 5](../2026-10-01-g6-effective-certification/PROOF.md), its [independent source review, section 4](../2026-10-01-sol61-g6-independent-review-2005z/REVIEW.md), and the [RAW NONPLANAR extension](../2026-10-01-sol61-head-audit-1956z/G6-NONPLANAR-FINITE-CERTIFICATION.md) are reused. New local inputs are [rational density with exact cut guards](RATIONAL-SOURCE-DENSITY-WITH-CUT-GUARDS.md) and its [support clarification](RATIONAL-SOURCE-DENSITY-SUPPORT.md). [Exact input identities](CELL-WITNESS-TO-RATIONAL-CLOUD-INPUTS.json) distinguish inherited arguments from this consumer.

## A finite cell has arbitrary real members and a computable witness

Fix species, one inheritance mode, target Z, a finite profile, and rational 0 < epsilon < 1. A row is one joint genealogy/bin observation; the profile metric is maximum row TV. Use the inherited same-target positive representative bound at error epsilon/4, with M at least every row's copy count and the species count. Enumerate its finite admitted graph catalogue and all age/cut weak orders. Retain parallel physical edges and the RAW NONPLANAR graph tests.

For each graph and weak order use one positive original rate rho_e for each whole physical population, including the ancestral population, and one original inheritance value per hybrid, shared across all rows. Hazard conditions are polynomial constraints

    h_e,j = rho_e (age_(j+1) - age_j).

They include original positivity, temporal admission, exact cut/node equalities, and every shared-variable constraint. The hidden source quantified by the theorem can have arbitrary real parameters. Exact real-closed-field feasibility of this finite rational formula returns a yes/no answer and, for a retained cell, a positive real-algebraic witness theta_w. This follows from real-closed-field decision and witness construction; it does not recover the hidden source or require it to be computable. Solver UNKNOWN, a timeout, or a missing witness is not a negative feasibility result.

All numerical constants in this exact feasibility step must have the declared rational/algebraic encoding. Arbitrary computable-real equality tests are not supplied by this argument.

## Within-cell source comparison uses physical hazards

Let P=(E+1)(V+J+2), U=P+r+1, C=choose(M,2), and A=max(C,M,1), as in the inherited proof. P overcounts finite physical-population operations per row, r counts original hybrid coordinates/boundaries, and the final completion is covered by the remaining unit. Choose

    delta = epsilon/(8 U A),
    integer H >= 1 with 2 U C 2^(-H) <= epsilon/8.

Partition hazards into cells of width at most delta below H and the saturated cell [H,infinity); partition inheritance into cells of width at most delta. All rows use the same variables and one joint feasibility test.

For two actual positive banks theta and theta_w in the same cell and weak order:

* An unsaturated population hazard differs by at most delta. Couple the same finite coalescent forest over the common hazard interval. The extra interval causes a merger with probability at most C delta, uniformly over the entering full forest.
* For two saturated hazards, compare each actual kernel with the common H-truncated physical-population kernel. Each costs at most C exp(-H), because a later difference requires at least two ancestors surviving at H. The triangle inequality therefore costs at most 2 C 2^(-H). This uses an auxiliary clipped kernel for a bound, not an admitted replacement source.
* COMMON couples each original hybrid bit once per locus, including unused latent slots. Its total cost is at most r delta. Every boundary reads the retained bit. INDEPENDENT couples coins on the actual current roots at each original boundary, costing at most M delta per occurrence and at most r M delta in a row. The count concerns current roots, not independently re-coined old tips.

Within an epoch, different populations act on disjoint live forests. They may be composed in a fixed canonical order because this profile omits relative ranks of unrelated mergers within the same bin. Their same old subtrees, physical population IDs, and bin tags are retained. Actual deterministic demographic maps and the terminal ancestral topology completion do not increase TV. The terminal completed genealogy with a constant tail-bin tag is rate independent; its real waiting-time law is not.

Sequential whole-forest coupling therefore yields, for every row,

    TV(P_theta, P_theta_w)
      <= U A delta + 2 U C 2^(-H)
      <= epsilon/4.                                    (1)

The larger U deliberately covers both inheritance mechanisms. This is the inherited hazard argument applied to two genuine cell members; no independent epoch-rate fit, coordinatewise observation union bound, or conditioning on an invented past is used.

## Only the witness needs a local rational-clock enclosure

The witness theta_w has computable algebraic parameter names and the exact certified chronology face. Apply the local rational-density/backend construction to it, choosing one positive rational original bank theta_hat on the same graph and weak order, and one finite residual law L per row with

    max_row TV(P_theta_w, L) <= epsilon/4.              (2)

To implement this hand construction, first choose a bounded rational neighborhood of the single positive witness. Its algebraic inequalities certify positive rate lower bounds, inheritance bounds away from zero and one, and finite age upper bounds. Choose fixed cutoffs K_i using the factorial tail budget in that neighborhood. Then refine the rational age/rate/inheritance boxes and the rational bank until the actual rate/inheritance common-law and upper-mean residual bounds meet (2). Exact cut equalities remain equalities. One bank serves all rows.

The finite coefficients of L are rational: residual count coefficients use rational means and finite Taylor denominators; the actual choice/boundary/initialization maps use rational bank coefficients; supported ancestral completion uses finite uniform ordered-pair choices. The residual mass is assigned to the entering state as defined by the accepted backend, rather than discarded or renormalized. The [support clarification](RATIONAL-SOURCE-DENSITY-SUPPORT.md) carries every numerical endpoint through the actual valid source support before completion. This is a mathematical finite calculation; executable enumeration and formal coefficient correspondence still need implementation and verification.

Theta_hat need not remain in the nonlinear hazard cell. It is a genuine same-target positive source on the same chronology face, and L only needs to be near the admitted witness theta_w. Thus rational density on the original affine chronology face is sufficient; no rational-density assertion inside an arbitrary nonlinear cell is introduced.

Nor is a global uniformization box imposed on all cell members. A saturated hazard cell can contain unbounded rates and widely varying clocks; the global uniformization rate also counts inactive populations. The local q, upper means and K_i may depend on theta_w. Applying the local rate-ratio estimate uniformly throughout such a cell would not be justified. Finite cells and a terminating local procedure for each witness are enough for a finite terminating mathematical construction, without an a priori practical runtime bound.

## Both cloud directions and emptiness

Output L for every retained jointly feasible cell, including its finite rational probability rows. Each L is within epsilon/4 of the admitted same-target witness law by (2), so the reverse Hausdorff direction is certified even if L itself is not an exact source law.

Conversely, every bounded admitted source belongs to some retained cell and is within epsilon/2 of that cell's L by (1)+(2). Every arbitrary finite admitted original source has the same-target bounded representative at epsilon/4 error. Hence its profile law is within 3 epsilon/4 of an output point. The cloud is finite and the profile simplex is finite dimensional, so passing to the target-image closure preserves this bound. Together,

    Hausdorff(cloud, closure(original target image)) <= epsilon,

with slack. Empty actual image gives no feasible cell; nonempty actual image gives a representative, a cell, and an output. No independently feasible row or epoch is promoted to a shared-source witness.

This remains an assembly of independently accepted hand inputs and the new hand consumer. Full G6 closure still requires the source-connected contextual representative consumer, actual sorted-cut/bin-history formal adapter, complete joint feasibility/enumerator implementation, rational probability correspondence, both certified distance directions, and the statistical/stopping/noise consumers. The queued bank proof drafts are not compiler evidence. Exact positive-source attainment and general G3 recognition are separate obligations.

Next action: independent review of the algebraic-witness quantifier, two-sided saturated hazard cost, once-drawn COMMON register, local-only clock budget, numerical support, and both Hausdorff directions; then preserve a typed consumer without replacing any of these gates by an assumed oracle result.
