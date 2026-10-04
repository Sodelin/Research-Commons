# Capture-avoiding identity successor

The immutable v1.2 candidate had a generic encoding flaw. If a source parameter
was spelled h0_0, it could coincide with a generated observation symbol. The
compiler then lost a repeated-row source equation in its inverse region.
Whole-policy verification on reachable histories did not repair the advertised
equivalence of that region with actual source-history existence. The independent
reproducer and its exact failed-manifest receipt are preserved under
`prior-failure/` in this successor.

The correction uses typed Dummy identities for source and history expressions,
simultaneous source xreplace, fresh backend auxiliaries and an explicit check
before printing observation-only guards. Original source labels survive as
provenance metadata. It does not reject legal input names to obtain a NO result.

The original nine-image compiled-policy checks were regenerated against this
source correction. Six cross-namespace controls additionally check both feasible
and impossible histories. The same original source provider, policy verifier,
positive domains and resource limits remain bound by the file manifest.

This successor remains unaccepted until a new independent review binds its
exact manifest. Generic nonlinear projection, singular/rank-changing source
coverage, automatic action search and general G7 synthesis remain open. Earlier
accepted supplied-policy and algebraic-section packets are unchanged.
