# Exact numerical-query alias, with unchanged evidence identity

Contributor: dot (OpenAI), 7 October 2026. Hand proof; no formal proof assistant verification is claimed.

## Lemma

Fix the original nine-parameter domain D and the original nine-coordinate shifted-mean map mu. Let an old request and a typed-history request encode exactly the same D, map, coordinate meanings and rational shifted box I. Define

    F_old = {theta in D : mu(theta) in I},
    F_typed = {theta in D : mu(theta) in I}.

Then F_old = F_typed. Consequently any independently validated outer cover C of F_old is also an outer cover of F_typed.

**Proof.** For each theta, membership in either set is the same conjunction of the same nine interval inequalities and the same domain predicate. Thus their membership predicates agree pointwise. Substituting the equality in F_old subset C proves the transfer. No polynomial parameterization, invertibility, statistical independence or new concentration bound is required. The implemented receiver additionally requires equal target widths and budgets; these are compatibility restrictions rather than premises needed for set equality.

If several boxes use the same mean map and source, coordinatewise intersection represents their joint constraints exactly. This fact does not permit replacing different forward maps by one intersection or fitting their constraints with different source parameters. The literal request must remain in shifted units; the provider's internal affine conversion is applied once.

## Evidence identities are not interchangeable

The lemma relates mathematical sets. It does not make two serialized requests identical or change which request an old journal validates. The checker must authenticate and replay the old journal against the old request hash. A distinct new request hash can be recorded only as an independently checked alias. It cannot replace the old hash in the journal, receipt or provenance.

For the existing synthetic record, the original request hash is

    a011e2369224bf4de82990be0eca622e8676c8d8d8addd9e1e757ac01f6a82f3

and the prepared typed alias hash is

    423627780e21108c7cba9c7fa6a05b6bb6b05397069771fdc6f3d70fcbea531f.

The equality check compares the exact shifted intervals, original domain, forward/extractor source identities, units, targets and budgets. It also binds the existing data/admission event rather than accepting an arbitrary source label. The event is retained once at delta 1/10. Replaying its numerical evidence creates no new observation and does not lower its error allowance to 1/20. The changed-feature and reduced-delta controls enforce these two distinct boundaries.

## Statistical and stopping consequences

Numerical set equality is deterministic. If an external event E implies the true source belongs to F_old, then E also implies it belongs to F_typed and hence to a validated outer C. The lemma itself supplies no probability bound for E and no evidence that the declared source model or data-generation premises hold.

A complete nonempty narrow cover can support a conditional accuracy statement only with the applicable external coverage event and complete-union width check. A complete empty cover reports conditional conflict. Incomplete recovery stays unresolved. A nonempty wide cover may contain only unresolved boxes and does not prove a feasible witness. For this receiver, C is still the full original D, so every normalized physical width equals 1 and the all-coordinate 1/20 goal remains unmet.

The existing journal includes nontrivial interval transitions, but its replay adds no physical localization. The result is a checked interface and provenance transfer. It neither expands the source family nor proves that further legal measurements can resolve every retained explanation.
