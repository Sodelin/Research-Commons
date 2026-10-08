# Conditional confidence and abstention

The implementation is deliberately a finite POINT catalogue, not the full continuous G6 source-image/closure catalogue. All candidate forward laws are exact rational probabilities. Computational error is zero for those points; no truncation/net guarantee is claimed.

For every predeclared experiment row e with D_e output coordinates, use alpha_e = alpha / number_of_rows. After k unique fresh loci in that row, the usual Hoeffding/coordinate/time union bound permits

    b(e,k) = sqrt(log(2 D_e k(k+1)/alpha_e)/(2k)).

The program uses the **larger exact rational** radius

    B(e,k) = min(1, upward_sqrt(ceil(log2(2 D_e k(k+1)/alpha_e))/(2k))).

Here ln 2 < 1 gives ln R <= ceil(log2 R). `ceil_log2` uses exact integer/rational comparisons and `sqrt_upper` uses integer square root with an upward correction to 1e-9. No floating-point probability comparison is used. When the expression exceeds one, radius one is valid trivially because probability-coordinate error cannot exceed one.

For each coordinate, Hoeffding failure is at most alpha_e/(D_e k(k+1)). Summing over D_e, all k>=1 (sum 1/(k(k+1))=1), and the finite row menu bounds the total failure probability by alpha. Within-locus coordinates need not be independent for this union bound. Each row's fresh loci do need the stated iid/fixed-law contract; cross-row selection before seeing the fresh outcome does not create extra copies of a locus.

At EVERY acquired prefix, keep a candidate when every coordinate differs from that prefix's empirical value by at most B(e,k)+eta. A removed candidate never reenters. Thus the compatible set intersects all prior constraints rather than only the final fixed-time interval. On one event of probability at least 1-alpha, the true listed source survives every observed prefix, provided its fixed observed row law is within eta of its exact clean law.

- If the survivors agree on the requested target, output a conditional certificate **within the declared catalogue**
- If survivors disagree, abstain and list alternatives
- If none survive, abstain with a model-or-confidence conflict; do not output a target

Assumptions: the true source is one of the declared points; the target labels are meaningful; row/menu and target are predeclared; loci are genuine fresh independent units with fixed row laws; eta is valid; every candidate row uses one shared source assignment. The program validates input structure and prevents obvious same-ID pseudoreplication. It cannot establish these scientific assumptions from IDs or sequence strings.

No globally uniform hidden-size bound, positive separation, eventual termination, calibrated sequence channel, full biological target, continuous closure approximation or optimal locus budget follows from this finite implementation.
