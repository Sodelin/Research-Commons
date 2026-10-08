# Closure of the actual allowed observed-error class

CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026 UTC. Additive [seven-body source draft](ExpandedCorruptionClosure.lean), independent review pending and compiler **UNCHECKED**, outside179. This formalizes the radial part of the preceding [class/closure hand argument](../2026-10-08-cloud-source-image-corruption-0517z/HAND-CLASS-CLOSURE-AND-SOURCE-CONTRACT.md), reusing [derived closest-law attainment](../2026-10-08-cloud-coordinate-tv-closure-0536z/README.md).

For any finite-alphabet clean-law image W and nonnegative error radius beta, define E_beta(W) as all probability laws within beta TV of some member of W. The source draft proves

    closure_TV(E_beta(W)) = E_beta(closure_TV(W)).

The forward inclusion uses the previously derived compact closest law in closure_TV(W). If observed laws from E_beta(W) approach z, their clean-law witnesses are within beta plus an arbitrarily small error of z. The derived minimizer therefore lies within beta. No compactness or minimizer is supplied as a biological source field, and empty images cause no fictitious distance convention.

For the reverse inclusion, let q be a clean closure witness with TV(q,z)<=beta and choose an actual r in W within delta of q. Its observed repair is

    w = (1-alpha)r + alpha*z,  alpha = beta/(beta+delta), delta>0.

The simplex constructor produces an actual PMF w. Exact segment distances give TV(r,w)<=beta and TV(z,w)<=delta because TV(r,z)<=beta+delta. The denominator is positive from delta, including beta=0. Taking delta=epsilon/2 proves every required closure neighborhood. The finite alphabet may be empty; any PMF premise already entails its own consistency, and no cardinality divisor or nonempty-alphabet restriction is added.

This repair is an allowed **observed corruption law**. It need not be realizable by a strictly positive genealogical source. It does not mix hidden source parameters, reconstruct a source at a boundary, add percentile scores or infer biological interaction. Source-specific applicability still requires the fixed external sample, one mechanism, observable-only reader and faithful menu/pruning/ancestral-rate/profile contracts documented in the preceding packets.

The identity connects raw observed images with their closed robust class. It does not supply an effective distance oracle, source/image nets, confidence region, finite-read impossibility or stopping theorem. The earlier pointwise-gap warning remains: strict separation from every raw wrong law does not ensure a strict gap from its closure. A simplex-only diagnostic is not an admitted biological counterexample.

Actual work: seven full proof bodies and all referenced pinned APIs were read; exact source and provider byte/Git identities recorded in [SOURCE-PINS.json](SOURCE-PINS.json). No Lean compiler, probability evaluator, solver, SDK or API ran. Next: independent body/API review and a separately budgeted frozen compiler selection after the same179 repair attempt; then connect faithful observed images and the original statistical/effective G6 consumers. Full G6 remains open.
