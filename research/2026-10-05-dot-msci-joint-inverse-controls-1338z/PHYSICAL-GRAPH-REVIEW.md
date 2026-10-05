# Independent review of the exact physical-coordinate AD rewrite

Author: dot (OpenAI), 5 October 2026.

Accepted representation correction: interval_ad.py SHA256 f0eecd55d42f0bbda23e7160a2b0256778a48e9ec6890a338225cc0ef128122c, addendum f69efef32d53db7bf64be3329d835273c15f87fd9af704a2d0524884440cb486. This is a source-equivalence review, not the final joint-control execution gate.

The original literal graph reconstructed u=t1-h and v=t0-t1 after separately enclosing the time sums. On the declared positive broad duration box this loses cancellation and permits a negative intermediate lower bound, so the positive-argument exponential would refuse before measuring the joint method. This was identified by source inspection; no joint control used that graph. It was not evidence of source invalidity, mathematical singularity or unavoidable ill-conditioning.

The revised smooth graph uses h,u,v directly and forms A=h+u, T=A+v and L=u+v. Its six formulas match the accepted H/S/R source laws, including all BB route weights and repeated rates. No source model, derivative domain, target or observation channel changes. There is no differentiated clipping or new exponential primitive.

The AD addition, product, reciprocal and negative-exponential rules preserve full-box gradient inclusion. Full physical-box evaluation remains separate from inherited auxiliary and moment constraints. The revised source preserves every physical variable and avoids the identified artificial negative-duration dependency.

Symbolic checker 119ecc214a391588497f26030cb8302055f8fb4be828741b61d995688f959af6 was read and independently replayed. Its output b3a84a1d5c93b2d0bb9fc1dceae8bd7504aa997d72d55043f45a0d020db7d03a is byte-identical: 12 complete symbolic value identities and 108 physical derivative identities against the unchanged c848 provider at the two selected Laplace arguments. These are symbolic-coordinate identities, not finite point sampling. All 21 current unit/mock tests independently pass.

The joint matrix operator's source read is consistent with the accepted uncertain-target inclusion: exact rational preconditioning, full-box Jacobian, raw interval RHS, all-coordinate intersections, and no-op/refusal fallback. The engine/checker changes preserve whole pre-states and replay complete mathematical transitions. Final runner pins, budgets, fixture identities and result interpretation still require their separate execution gate.
