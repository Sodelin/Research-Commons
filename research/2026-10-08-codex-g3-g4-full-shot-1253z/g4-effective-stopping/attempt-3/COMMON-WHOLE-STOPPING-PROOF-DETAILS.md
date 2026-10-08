# Details supplement: projectivity, integration bound and exact tree catalogue

Contributor: Codex role 5, 8 October 2026. Additive companion to `WHOLE-COMMON-DIRECTED-PATH-EXPOSURE-AND-STOPPING.md`. SOURCE/HAND candidate, review pending. No mathematical execution or compiler was run.

These details make the three main source gates independently checkable. They do not broaden the main theorem's whole-network/full-topology/COMMON/finite routing-only menu/effective-field contract.

## Selected-label restriction in the actual conditional process

Conditional on the finite whole COMMON/program configuration, all selected and unselected copies follow one ordinary population tree. On an edge, track the ancestral roots carrying at least one selected label. A merger of two such roots has rate one for each selected pair. A merger with a root carrying no selected label changes neither the selected partition nor its restricted genealogy. A merger of two unselected roots is likewise invisible. Restricting the full Kingman genealogy consequently gives exactly the smaller selected-label Kingman process, with opaque restricted genealogies substituted at the next edge. At population pooling, restriction commutes with pooling. At a COMMON hybrid or fixed program choice, the one same chosen parent routes every selected carrying root, so restriction commutes with routing. The same argument applies through the infinite ancestral completion. Finally average once over the original finite joint configuration distribution.

Therefore summing actual final-topology outcomes by their selected-label restriction produces the smaller allocation law. No hypothetical separate route or deterministic program row has become an observation. This proves the specific projectivity used by the pair caterpillars, rather than assuming that an untyped hidden kernel is observable.

## A uniform-in-N bound on compatible finite-edge histories

Fix one positive stem-free ordinary n-taxon tree T. It has e_T finite edges. In the alltaxon-first caterpillar, the allowed pre-root prefix mergers are the fixed labelled prefixes of sizes 2,...,n-1. A pre-root history has a number s in {0,...,s0}, s0=n-2. Its merger list is a prefix of that fixed sequence, since a later prefix cannot form before the earlier one. Assigning these s events to finite edges yields at most e_T^s assignments. Invalid assignments contribute zero, so counting every assignment is a safe upper bound.

For a valid assignment, let r_e be its number of events on edge e. The ordered time integration on that edge has volume at most t_e^r_e/r_e!. Each designated current-pair merger has rate one. At all edge times, at most s0 labels have been removed by actual mergers elsewhere in the genealogy. Its current root count is therefore at least N V_e-s0. For N>s0, this count is at least two and the total exit rate is at least binom(N V_e-s0,2). Thus its complete finite-edge no-additional-merger density is bounded above by the exponential in the main proof's (10).

One explicit constant for summing all ordered integration volumes is

    C_T=(sum_(s=0)^s0 e_T^s) (1+sum_e t_e)^s0.

All factors are finite and independent of N. This deliberately overcounts assignments and volumes; it is used only for a proof bound, not computed by the stopping algorithm. Completing the one opaque compatible prefix at the displayed root has probability kappa_(m-s), hence the exact ratio bound in the main proof gives

    P_T(G_N)<=kappa_m C_T m^(2s0)
      exp[-sum_e t_e binom(N V_e-s0,2)].

The displayed MRCA root is the only root used in this calculation. A finite original path above that displayed root is already absorbed into the infinite ordinary completion. Leaving it in the finite-edge product would create a false quadratic coordinate and would invalidate the n-2 pre-root count. The original physical retained root is unchanged in the network.

## Finite exact catalogue without logarithmic computation

Given the product of directed grids, examine each full tuple b_(i|j). Set a_i to the exact algebraic minimum over j and z_ij=a_i/b_(i|j). Reject if z is not symmetric or any z_ij is outside (0,1].

Enumerate all finitely many rooted binary labelled n-leaf tree shapes. For each shape, every internal node w has two nonempty child taxon sets. Choose any cross-child pair i,j and assign the node the coordinate z_w=z_ij. Verify that every cross-child pair at w has this same value. Require the root coordinate to be one. For each internal child w of an internal parent p, require 0<z_w/z_p<1. For a taxon i with parent p require 0<a_i/z_p<1. These are exact algebraic equality/inequality checks. The ratios are the edge survival coordinates.

These checks reconstruct precisely the positive binary stem-free ordinary tree matching the full directed tuple. Incomparable internal nodes may have equal z; only parent-child ratios must be strict. No logarithms, generic-rank assumption or forbidden zero-length edge is used. Every actual conditional tree of the target or any matching rival passes at least one shape check. Duplicate shapes/tuples giving the same entire a,z covariance are merged exactly before the rank search. The covariance uniquely determines the hierarchy because every positive internal edge produces its proper descendant cluster and its strict parent-child level; hence this deduplication preserves every distinct ordinary response profile.

The rank search then evaluates only actual positive ordinary tree probabilities at exact algebraic edge survivals. Although a grid tree need not itself be realizable as a configuration of the unknown whole source, its ordinary genealogy law is well defined. It is a matrix column, not a claimed physical mixture realizing that source. The later same-theta graph catalogue is where actual source realization is required.

## Retained-core marks versus unknown source count

The protection count h is the finite public set of sites/edges/template marks whose identity or imposed parameter relations must survive a physical reduction. It is not the unknown total reticulation count. The unmarked retained-core theorem is what bounds all other branching/root blobs independently of that unknown count. An interface that declares every unobserved edge protected or permits infinitely many unprovided ID constraints would fall outside the source-budget part of this theorem; the response stopping proof would still require its own explicit finite authorized menu.

The whole-source stopping proof uses no supplied graph-template size. Its core-free response argument in Sections 2-7 of the main proof is independent of h. The actual representative bound in Sections 8-9 additionally uses the original finite protected-mark grammar. These two conclusions must not be conflated.
