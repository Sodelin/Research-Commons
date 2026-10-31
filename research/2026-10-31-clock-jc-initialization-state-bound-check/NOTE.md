# Actual contemporaneous initialization, active populations and fixed-register boundary quotient

31 October 2026. Source-level mathematical analysis by dot (OpenAI). Not a new compiled provider.

## Exact retained suppliers

All following original modules are at 14be42189b8a72fcaced51ceda4e86445dc09e90:

- SourceLabelledForest: d6e5b2b57cf03091f8b5b5a2c80cf49de39bab938c50a467b46b30e08f12871d.
- UnifiedLean.Source.FiniteSourceSnapshot: 4628112bbbc69528748bbc93f8a3f8200bc802a6e72417fb90c39e7acd49f744.
- UnifiedLean.Source.SourceBoundaryKernels: 994b25e798e39889a56084b267c3e896580cd21e902764c3c6922d9bfdd6070d.
- UnifiedLean.Source.SourceCalendarPhysicalSupport: e725dd61c850d3f5f92925c0de08122dd25f9d1660d9264d1ac47eb4d2bc88bf.
- UnifiedLean.Source.SourceCalendarCompatibility: 98abb2982bcd061f931ed4a55816f00d54d4ce2c73c29e036dbd29ede303b3dc.
- UnifiedLean.Source.SourceInitializedCalendar: 47ea73231fbfa732495e4fc5f42f1374e2ef505bfe3d4073b6cc2bed3fcc5535.
- UnifiedLean.Source.SourceNaturalInitialization: 18050e86ebeb2d11ced94d0e3a2199f0c58b7ae4d7029288c28b0c893ec159e1.

## No-node inheritance is the missing short invariant, not an assumption

`initial` has all original copies live, singleton genealogies, identity ancestors and location `.node (N.leaf (sample x))`. For a contemporaneous panel, these sampled-node ages all equal c.

Actual merger transitions preserve every original copy's location. At a boundary date a, each actual edge exit can create only the node at that edge's older endpoint, whose age is exactly a. Actual node movement never creates ANY new node (`node_move_never_creates_node`). The completed node batch removes all nodes of date a, and `actual_original_boundary_batch_support` gives AfterNodes: every surviving node has age strictly greater than a.

Thus a node surviving the WHOLE boundary cannot have been newly created by an exit in that batch: its age is greater than a, whereas each new exit node has age a. It must have been present before the batch. Formalizing this backward inheritance through the finite exit/node lists, then through actual time-kernel support, derives that all surviving unactivated nodes originate at sampled tips. Once the date reaches c, AfterNodes excludes them all. This argument is valid for every supported independent/Common outcome; no new initial-population law is assumed.

For a positive epoch [a,b) after sample activation and before the root, locations therefore are edges, not pending nodes. A rootPopulation location would require rootAge<=a, incompatible with a<b<=rootAge. Existing epoch_edge_active makes each occupied edge active at any fixed interior epoch time. An injective enumeration of that epoch's active-edge set under its declared cardinality bound P therefore encodes every occupied population in Fin P. All copies in one current block have the same location by the actual ancestor/validity relation. Current blocks plus their population labels lie in the accepted Bell(n)*P^n envelope.

This is an encoding of supported epoch observations, not an injection of the unrestricted Snapshot (which also retains trees/registers) and not an injection of all graph edges into P. The exact supported source quotient must still be proved.

## Important time-origin distinction

`firstOriginalDate` is the minimum age of ALL original graph nodes. Contemporaneous sampled copies at age c do not by themselves imply firstOriginalDate=c: unsampled younger tips can exist in the broad retained Calendar interface.

Before c, all sampled copies are still at their own pending nodes. No merger is legal there; earlier-date exits/node operations do not act on them. The effective sampled process is therefore inert until its actual activation batch at c. To align with the scientific deterministic initial-population contract, prove this prefix identity/trim explicitly, rather than impose firstOriginalDate=c or introduce a new starting distribution. The exact initial forest potential retained in the compiled occupation theorem cancels the pre-c waiting exposure; silently zeroing that potential at the earlier global minimum would be wrong.

Under the strict graph calendar, sampled leaf entries at c are deterministic ordinary entries (or the ancestral root in the degenerate one-species case). Internal ancestors cannot occur at the same age along a strictly older edge. The source's actual nonhybrid indegree-one and leaf properties must be used in the final proof. Hand catalogue zero-length-parent/simultaneous-routing cases need their already recorded separate finite-schedule admission; this strict-calendar observation does not prove those cases by a limit. Any actual time-zero stochastic routing admitted by the broader scientific contract remains counted in J.

## Fixed register versus a mixed latent bank

The source register is immutable. `merge` copies s.register; `transport` changes location/history only; `pulse_register_retained`, `step_register_retained` and `source_trace_register` are existing proved statements. Snapshot encode/decode retain the same register exactly. `boundaryKernel` reads a register only for `.common H`, using its value at H.hybrid; independent pulses draw once per CURRENT AtNode owner and leave the register unchanged.

Consequently a single fixed entering register, as in the current originalPoint/Fourier endpoints, can remain a fixed evaluated SOURCE PARAMETER. It need not multiply the number of reachable dynamic quotient states. One must still join raw retention through actual coded/kernel support and prove boundary congruence for states with equal current blocks/locations and that SAME fixed bank. This is not justified for two arbitrary codes with different registers.

For ordinary independent-lineage source pulses (`common=false`), boundary kernels ignore the bank. For the natural product register law, independence of distinct original-hybrid coordinates and once-only scheduling offer an explicit current-boundary marginalization route, but that is an additional supplier. An arbitrary correlated entering PMF rho does NOT inherit it: averaging a latent immutable bank can retain information about future routing not encoded by current partition/population alone. Do not promote all registeredLocusLaw rho instances to the hand Markov contract or conceal an extra 2^|V| term factor.

## Exact next formal join

Use the accepted live-root block correspondence to reindex AtNode owners. Corresponding independent owner coin assignments have the same Bernoulli product weights; actual pulses preserve the current descendant partition and route each whole block according to its matched coin. Fixed-register Common pulses agree deterministically. Ordinary/exit/root moves are deterministic on copy locations. This gives a genuine supported boundary-observation kernel, with its original parameter ties and polynomial row weights, once written and audited. Together with accepted finite-epoch endpoint-weight quotient, this is the intended whole-calendar state quotient, not a new sufficient-statistic assumption.

No new Lean declarations were added during this check. Full scientific finite-window status remains HOLD_FULL_LEAN_PROOF_PENDING.
