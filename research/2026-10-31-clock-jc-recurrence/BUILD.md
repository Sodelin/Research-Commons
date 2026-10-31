# Reproduction with immutable dependencies

Use Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` with its pinned manifest dependencies. Obtain those sources/objects under their ordinary provenance checks; this packet does not certify downloaded dependency archives. Both modules import only Mathlib or the first local module; exact imports appear in SOURCE-MANIFEST.json.

In an isolated project using those dependencies, copy `lean/ResearchCommons` to the project source root. Compile JC69ExponentialPolynomial before JC69CountVectorGrid, then run the exact NamedAudit.lean and the portable OwnedAudit.lean with `lake env lean`. For explicit commands from the project root:

```sh
lake env lean -o ResearchCommons/MSCI/JC69ExponentialPolynomial.olean ResearchCommons/MSCI/JC69ExponentialPolynomial.lean
lake env lean -o ResearchCommons/MSCI/JC69CountVectorGrid.olean ResearchCommons/MSCI/JC69CountVectorGrid.lean
lake env lean audit/NamedAudit.lean > NamedAudit.log
lake env lean audit/OwnedAudit.portable.lean > OwnedAudit.log
```

Set the local project source root on LEAN_PATH if the enclosing package does not already expose it. Compare exact source hashes, eight named types/axioms, selected two-module set and complete audit metadata against the preserved receipts. Reproduction commands are instructions, not a claim that they were rerun for publication. Original immutable sources and audit outputs remain the authoritative successful record.
