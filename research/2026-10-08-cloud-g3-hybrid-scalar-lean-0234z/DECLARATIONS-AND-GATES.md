# Declared scalar scope and actual-source gates

All names are in `CloudG3.HybridSizeCore`. **All source declarations below are UNCHECKED until an actual compiler receipt exists.** Their hand mathematics follows the accepted corrected source-size proof; preserving a proof body does not establish elaboration.

| Name | Kind | Exact role |
|---|---|---|
| `cellT` | Definition | Four-variable scalar polynomial; not an admitted biological source |
| `drop_v_identity` | Theorem | Exact polynomial difference when v is removed |
| `push_u_identity` | Theorem | Correct factor `(p-u)(2p^2+2pu-u^2)`; no false square identity |
| `quartic_gap_identity` | Theorem | Exact square-factor identity for `27/256-p^3(1-p)` |
| `cubic_product_le` | Theorem | Polynomial upper bound for every real p; stronger scalar fact does not broaden source admission |
| `drop_v_le` | Theorem | Requires nonnegative p,q,v and `v<=u` |
| `push_u_le` | Theorem | Requires nonnegative q,u and `u<=p`; derives every needed factor sign |
| `cell_swap` | Theorem | Exact p/q and u/v swap symmetry |
| `boundary_identity` | Theorem | Exact `T(p,q,p,0)=-(4/3)p^3q` |
| `complete_cube_cell_lower` | Theorem | Requires p,q,u,v nonnegative, `p+q=1`, `u<=p`, `v<=q`; covers both order regions and all boundaries |
| `corner_contrast` | Theorem | Exact scalar attainment at p=3/4,q=1/4,u=3/4,v=0 |
| `constant_residual_budget` | Theorem | Derives `(13/256)b<=e+cb` from `b>=4/27`, `t>=-9/64` and exact `e=t+b(1-c)` |
| `pow_unit_interval` | Theorem | Proves nonnegative powers and `a^k<=1` from `0<=a<=1`, using direct finite induction |
| `discounted_step` | Theorem | Requires `0<=a<=1`, nonnegative c,e, `ab<=e+cb`, and `ba^k<=G`; NO upper bound on G |
| `ordinary_step` | Theorem | Requires b nonnegative, `0<=a,c<=1`, and `ba^k<=G`; preserves the same count exponent |
| `discountGap` | Definition | Finite scalar recurrence `G0=b`, `G(k+1)=e(k)+c(k)G(k)` |
| `finite_discounted_lower` | Theorem | Requires every c,e nonnegative and every row budget; proves `ba^n<=G(n)` by induction |

The generic discounted step does not require b to be nonnegative: its explicit row budget, scale and tail inequalities suffice. The actual source application separately proves the stronger `b=-m>=4/27`. The ordinary step does require and retain b's nonnegativity. No theorem assumes `G<=b`; positive tails remain covered.

The following actual-source obligations are inherited hand results or future formal consumers, not conclusions of this scalar file:

1. Match `cellT` to the original natural INDEPENDENT routing/coalescence kernel and chronological completed-quartet readout, with the original opaque subtree/projectivity semantics.
2. Define the actual no-merger probability c, prove `0<=c<=1`, and attach the exact cocycle and the nonnegative residual `e=T-m(1-c)` to that same kernel.
3. Supply the signed continuous reward, compact effective algebraic minimum m, and the actual corner calculation giving `b>=4/27`. The prototype proves the contrast corner only; it does not independently derive the source discount `13/256` or define m.
4. Map the abstract finite recurrence to a literal selected-lineage factor list, handle ordinary passages with `ordinary_step`, and show the number of contributing hybrid cells is at most the original graph's TOTAL hybrid count H.
5. Attach finite positive source density, original graph embedding, exact positive leading padding and the simultaneous fifteen-coordinate observation law. The prototype does not construct those sources.
6. Preserve the original coupled input for arbitrary G3 observations, rather than substitute this passive quartet coarsening. General exact positive extraction and terminal NO remain open.

Pinned API inspection was read-only and limited to `pow_nonneg`, `pow_succ`, `sq_nonneg` and ordered multiplication signatures, plus imported tactic entry points. Source tactic elaboration, recursive simplifier behavior, generated declarations and complete transitive axiom audits remain unknown. The source has no custom provider imports and changes none of the frozen compilation targets. Next action: independent bounded source-semantic review; any later compiler selection belongs to the sole Lean owner after its actual terminal and root gate.
