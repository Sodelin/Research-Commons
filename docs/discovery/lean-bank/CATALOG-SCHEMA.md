# ProofBridge catalog v1

Offline catalog linking stable problems, theorem statements and pinned Lean artifacts.
No resolver fetches files, executes Lean, follows external instructions, or changes
repository state. Reported receipts are attestations indexed as supplied, not
independently authenticated or rerun by this tool.

```
python catalog.py fixture.json validate
python catalog.py fixture.json search "grid minor"
python catalog.py fixture.json show problem.alexander.001
python catalog.py fixture.json show theorem.host.minor
python catalog.py fixture.json show artifact.host.minor
python catalog.py fixture.json lock problem.alexander.001
PYTHONDONTWRITEBYTECODE=1 python -m unittest -v
```

## Schema

Top level: `{schema:"proofbridge.catalog.v1", problems, theorems, artifacts}`
where the three collections are arrays. Stable string IDs begin with
`problem.`, `theorem.` or `artifact.`, using lowercase ASCII letters,
numbers, underscores, hyphens and dot separators. Do not reassign an ID to
a different statement. Provenance for all row types is `{kind,reference}`
with kind `primary`, `internal`, `derived` or `external`; reference is
a nonempty citation or origin identifier.

- Problem: `{id,title,statement,closure,provenance}`. Closure is `open`,
  `partial`, `conditional` or `closed`. A closed problem requires a
  linked exact theorem that is not conjectural. Closure remains a catalog claim,
  not a Lean verdict or a worldwide novelty assessment.
- Theorem: `{id,title,statement,assumptions,problems,artifacts,provenance,proof_status}`,
  plus optional `uses`. The statement string is the complete preserved statement
  including its premises; `assumptions` is readable metadata for extra premises
  compared with the referenced question. Problem links are `{id,relation}` with
  relation `exact`, `partial`, `conditional` or `related`. Exact isn’t
  inferred: it requires byte-identical statement text and no extra premises.
  Proof status is `conjectural`, `hand_proof`, `checked_component` or
  `kernel_checked`. Artifact links are IDs. The optional theorem links are
  `{id,relation}` with relation `uses`, `may_use` or `extends`.
- Artifact: `{id,repo,commit,path,declaration,sha256,verification,provenance}`.
  `repo` is an owner/name. `commit` is full lowercase hex (40/64 digits).
  `path` is canonical repository-relative POSIX. Set declaration to null only for a file-level locator without a kernel declaration attestation. `sha256` is full lowercase
  SHA-256 of exact source bytes or null if uncomputed. `verification` is
  `{kind,reference,lean_version,statement_sha256}`. Kind is `source_only`,
  `remote_ci`, `local_replay`, or `kernel_checked`. Source-only has no
  populated attestation fields; remote CI/local replay require receipt reference
  and Lean version but not declaration-level identity. Kernel-checked requires
  source SHA-256 and SHA-256 of the UTF-8 statement string. This is identity, not
  an algorithm for proving equivalence between prose and Lean.
- Artifact lock: `{schema:"proofbridge.artifact-lock.v1",root_id,artifacts}`.
  Resolves artifact rows by immutable Git commit/path/declaration. For problems,
  includes their referenced theorems and transitive actual `uses` dependencies;
  for theorems includes their transitive actual `uses` dependencies.
  `may_use` and `extends` are inspectable but not hard build dependencies.
  Missing source-byte digest remains null: a commit pin is not a byte hash.
  This is an artifact locator lock, **not** a complete Lake/toolchain lockfile.

The included fixture is synthetic; it demonstrates that a partial theorem and
a known remote source do not close or verify the problem. The tests exercise
dangling references, artifact pinning, lower evidence tiers, reverse lookup,
identity mismatches, and false closure promotion.
