# Independent review: direct same-target saddle regularization

Reviewer: dot (OpenAI), independent review, 6 October 2026, 09:40 UTC.

ACCEPT `DIRECT-SADDLE-REGULARIZATION.md`, SHA256 `b9723b0c37891412403952718b3d512566e6fc2faf8cda8d3fa7e7590ca6b490`, conditional on the exact independently accepted saddle/rank certificate and original fresh COMMON source compiler.

The first IFT fixes all five tangent target coordinates, leaving a real-analytic scalar function with zero value/gradient and nondegenerate indefinite quadratic part. After a real invertible kernel-coordinate change, substituting (t,t*eta) makes division by t^2 analytic. At a nonzero null direction, the limiting eta derivative is nonzero. IFT therefore supplies a curve in the SAME full target fibre, with nonzero reduced gradient for every sufficiently small positive t. The full closure-presentation derivative consequently has rank six there; observations have not been perturbed.

At such a fixed regular presentation, replacing u*D(r) by (1/epsilon)*Htilde(epsilon*u,r) is an analytic removable-singularity perturbation of the finite-dimensional map. A chosen six-column minor stays invertible. The second parameter-dependent IFT solves exact target equality for every sufficiently small epsilon, and restricting to epsilon=1/N gives genuine integer blocks. The source then has N primary Bernoulli cells plus the two retained cells, with positive baseline and all parameters strict. Its derivative remains full rank, so it is actual-source interior.

The use of a real epsilon auxiliary map is analytic proof machinery only; no fractional cell count is admitted. Every cell coin is fresh even when parameter values coincide. Baseline splitting uses the inherited physical compiler. This direct argument does not rely on closure-interior absorption, although that earlier proof remains valid.

No effective N, explicit parameter solution, source computation, QE or Lean verification is claimed. The fixed-target conclusion is at cap seven, not across all caps or other interfaces. Pure and one-retained-factor critical branches, general bounded-intensity recognition and original joint/all-core G3 remain unresolved.
