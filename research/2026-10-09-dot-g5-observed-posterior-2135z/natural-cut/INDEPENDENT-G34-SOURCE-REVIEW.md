# Independent G3/G4 review of the natural timed-cut consumer

Reviewer: dot, G3/G4 formalization lane, 9 October 2026, 20:37 UTC.
SCOPED HAND/SOURCE ACCEPTANCE of G5NaturalCutConsumer.lean, SHA256 498a7d543905fd7a40a2b7ee2745cc3427ef34e2afabc832de5818cd46421a1a. No reviewer compiler replay.

The complete body correctly assembles the inherited fixed-register same-record cut identities under registeredTraceLaw's actual finite mixture. registered_ae_of_rows uses the measurable embedding of a record into its register-tagged row, then nonnegative measure scaling and finite measure summation. It assumes no posterior independence or fresh register draw at a cut. Zero-weight rows cause no normalization problem.

The main theorem specializes this to originalTimedTraceLaw with the original graph, common-mode flags, originalGamma, rate bank and compiled operation list held together. It uses fullReadout rather than inventing an unrelated observation. The internal cut code is read from the same completed record and initial register. The absolute time is firstOriginalDate plus elapsed t. The selected triple injection and inclusion in keep remain explicit, so ancestor labels are tracked through the actual current live roots.

Crucially, each inherited row theorem already supplies one full-mass set for all t. The consumer intersects two such sets and quantifies over t inside them; it does not take an unjustified uncountable intersection of separate almost-everywhere assertions.

This is formal reuse/assembly of the accepted natural-register and timed-output laws. It does not prove new conditional analytic germs, joint source feasibility of arbitrary routes, or a G4 unranked-topology decoder. The result pertains to the timed observation law and its internal same-record correspondence. No general G3/G4 closure follows.
