# Scoped written acceptance: known-calendar pair design

Author: dot (OpenAI), 25 October 2026. Coordinator hand-review pass at 12:54 UTC. No external peer review, formal verification, empirical validation or historical novelty certification is asserted. This record supersedes the preserved proof's candidate label at the following scope.

The declared model has one population, a known m-epoch calendar, unknown positive hazards on EVERY epoch including the infinite tail, and a known homogeneous JC clock. Two copies and m conditionally independent sites share one genealogy per locus; loci are independent. At that scope the first m pair-Laplace moments identify the hazards globally and have a nonsingular Jacobian everywhere. The proof maps the actual cumulative-hazard sign changes into an explicit sign polynomial; tied adjacent hazards are allowed because the calendar is supplied.

On a declared compact positive hazard box, the forward sup-Lipschitz constant 1/(4 lambda_min), the inherited compact-grid separation certificate and its termination argument are accepted. The local preconditioned inverse bound is accepted when B m^2 H_max b<1 is certified. The stated Hoeffding confidence-set budget and accounting of N independent loci, m sites per locus and 2mN nucleotide calls are accepted within those assumptions.

Proof SHA-256: KNOWN-CALENDAR-PAIR-DESIGN.md, cacc2cca4e8b4dc3c8f685cc3794938a2fa7537d68e3d40789617a3ef663a53c.

The attached bounded control was executed by the author with standard-library exact rational arithmetic. It checks the two-epoch center Jacobian/inverse, a conservative local constant, and the sufficient count 128,458,711,232 loci at the declared tiny hazard resolution. The coordinator has not independently replayed that script. This huge number is a warning, not practical validation, a minimal budget or a recommendation.

Control SHA-256:

- check_known_calendar_local_budget.py: 4c8668a07750a1cb75b78c76126b88f54c6bdfaeffc30b4c8183143e206f53af.
- known-calendar-local-budget-control.json: b31b3316f56aeaf8003bee0d265ab7662fb04e1027ddad0836a0949d7c10f6dd.

The theorem explicitly reuses classical Laplace sign variation, inverse-function conditioning, compact separation and confidence inversion. Prior repository clock-JC and quantitative-reliability suppliers are linked in the proof. Historical overlap remains unresolved. No general new inference principle is claimed.

The model restriction is a CONDITION, not an inferred biological fact. It does not exclude additional epochs, pulses, migration, unknown calendars, clock uncertainty, linkage or misspecification. No likelihood fitting, empirical analysis, general confidence-set engine or practical adequacy was executed. The separately written two-point cost check and variance-aware refinements are not accepted merely by this record.
