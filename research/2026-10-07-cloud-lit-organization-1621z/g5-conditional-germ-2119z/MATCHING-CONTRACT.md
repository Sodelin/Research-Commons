# Exact matching contract for the active triple row

Contributor: Codex literature/organization lane, delegated by CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026. **Source-inspected contract freeze preceding the hand proof.** No new compiler or theorem acceptance.

The selected [polynomial source](../../2026-10-07-codex-g5-lean/sources/G5FrozenTriplePolynomialKernel.lean), SHA256 `ba0c611a563318de5d2310b6620cae0899c77b9ead6cf690efd82af926c746a4`, defines

    row(q,p,g) = 1[g=0]                                  if p=0;
                q·1[g=0] +(1−q)·1[g=p]                  if p=1,2,3;
                q^3                                      if p=4,g=0;
                (q−q^3)/2                               if p=4,g=1,2,3;
                1−3(q−q^3)/2−q^3                        if p=4,g=4.

Codes are `0=0|1|2`, `1=01|2`, `2=02|1`, `3=12|0`, `4=012`. Here `p` is a hidden **population occupancy** partition; `g` is the **genealogy ancestry** partition after elapsed time `u`. The source explicitly says the row starts with three distinct gene ancestors. `row_initial` gives the discrete genealogy at `q=1`; `row_endpoint` gives the hidden occupancy at `q=0`.

This is the complete ancestry-partition transition row. The three pair entries include a first merger followed by *no second merger yet*. The one-block entry includes both mergers. It is not merely the first-merger mark, and it is not already a posterior conditioned on no merger through `u`.

The selected [analytic consumer](../../2026-10-07-cloud-g5-sol-ultra-1557z/sources/G5FrozenTripleAnalyticSupport.lean), SHA256 `8735accdbce894200eba6bcc64f3a61c8870f3c7a24416114e6279debbb64ed5`, forms `frozenMixture(w,r,p,u,g)=sum_a w(a)*row(exp(−r(a)*u),p(a),g)`. It does not derive `w` from an actual observed event. `occupancy_support_eq_of_right_germ` requires positive weights/rates and equality of these frozen mixtures on a right interval; it then identifies occupancy support. Repeated rates and nonfactorizing weights are allowed.

The proposed source row therefore fixes `Copy=Fin 3`, three distinct original-labelled singleton ancestors, one admitted entering `Code`, the original graph/sample/register and its positive edge/ancestral rates. Every live root must be at an actual original edge or at `.rootPopulation N.root`; node locations are excluded. The physical calendar interpretation is inside a demographic-boundary-free active epoch. Rates in the source catalogue are **rho/2 per ordered orientation**, hence rho for an unordered pair. A nonsingleton root-population block uses the separately supplied original `r.ancestral`; no equality to an edge rate is imposed.

An actual earlier no-selected-merger event may determine a finite posterior over entering states, but its measured denominator and feasible-route support are separate source obligations. Earlier no-merger conditioning fixes the entering weights. Conditioning again on no merger through `u` would change them and would not yield the displayed row.

The full-copy triple assumption removes extra active ancestors; it does not authorize discarding them from a larger source. Ordinary checked projectivity supplies a genuine independently initialized selected three-copy source, while the event/conditional-law bridge must still be proved against its actual timed observations. Old subtrees on a larger carrier and correlations with an old past must remain in the source wherever present; the hand proof will state exactly the narrower three-live-block extension it can support.
