# Appendix: noise-aware reference truncation and its quantitative limit

19 October 2026. Contributor: dot (OpenAI).

**Reviewed reference result.** The frozen proof has passed separate assistant-context hand/source review and coordinating hand review. The independent same-source replay passed all 38 finite controls. Its historical candidate label is preserved; this README and the review record its current scoped acceptance.

For the interacting auxiliary reference B*=D0*+i[H,.], retain the exact on-site reset rate g=8b_min. Physical partial-trace oscillations give a volume-independent operator-norm truncation estimate for a fixed local observable O_X and a radius-r ball:

    ||S_t O_X-S_t^(r)O_X||_infinity
      <=3h|X| exp(-mu r) integral_0^t exp(a_mu s)ds ||O_X||_infinity,
    a_mu=3h[1+(k-1)exp(mu)]-g.

The proof allows arbitrary noncommuting Hermitian interaction terms under the original local incidence bound h. It uses complete positivity only for the auxiliary reference and specified reference generators with Hamiltonian terms removed. It does not assign positivity or contractivity to actual Redfield evolution.

This fills the operator-truncation premise of the [hypercontractivity appendix](HYPERCONTRACTIVITY-APPENDIX-README.md), but its sufficient graph-growth join still does not cover the original full class. On an admitted noncommuting three-body hypertree with fixed one-site root, branching 16, m=nu=19 and h=g/8, the resulting condition 2g mu>alpha a_mu fails for every mu>=0, even using the actual growth rate alpha=log(16). A favorable smaller bulk-column rate also fails the displayed constant test.

This failure concerns these sufficient constants. It is not a lower bound on physical propagation, a failure of true reference mixing, or a counterexample to P5. Some original parameter regimes do admit the derived estimate, including direct local reference mixing for k<=2. No polynomial-growth assumption, stronger noise condition, or narrower master problem is adopted.

## Evidence

- [Frozen proof](NOISE-AWARE-REFERENCE-TRUNCATION-20261019.md), SHA256 917f73e5869722e42bd7111ba3315bc11e76c7ebaf1ad60961e52cf48687585b: general operator argument, exact constants, geometry and thermal admission, and the optimized sufficient-criterion test.
- [Exact checker](noise_aware_reference_truncation_check.py) and [saved log](noise_aware_reference_truncation_check.log): 38 finite controls of projections, Pauli algebra, incidence, ball counts, bath-box arithmetic and polynomial inequalities.
- [Independent review](NOISE-AWARE-INDEPENDENT-REVIEW.md): general hand/source PASS and unchanged-checker replay with the same log. Replay is not an independently authored implementation.
- [Supplement manifest](NOISE-AWARE-MANIFEST.json): hashes and byte counts of these five files, excluding itself. Earlier packet files and manifests remain unchanged.

Thermal positive type and envelope are inherited from the cited reviewed bath supplier. No new bath integration, infinite-volume simulation, actual Redfield execution, Lean verification, external peer review or historical novelty is claimed.

The original same-H infinite-filter Redfield versus square-window GKSL plus triangular Lamb-shift comparison remains open for arbitrary finite volumes, all times and arbitrary initial states with fixed observable support. The remaining tasks are a sharper reference operator-norm join or direct control of actual signed forcing, including the propagated scalar output.
