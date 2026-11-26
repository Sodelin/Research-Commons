# Offline Lean source closure planner

The planner answers a deliberately restricted question: **which source files for these selected Lean entry modules are already present as exact pinned bytes, and which approved file reads remain?** It does not attest an operational GitHub connection, retrieve files on its own, run package-defined commands, set environment variables, invoke Lean, or claim a build works.

```sh
python closure.py config.json --source-store ./store --local-root ./packet
python -m unittest -v
python replay_thue.py ../omnibus-routes/thue-morse-reuse --output results
```

## Interface

Use config schema `commons.lean-source-planner.v1`. See `results/thue-fixture-config.json` for a concrete input.

- `version`: caller-chosen explicit staging segment; `toolchain`: caller's identifier, recorded, not verified.
- `targets`: finite explicit Lean module names. No default package-wide scan.
- `repositories`: external permission must already exist. For each approved exact owner/repo, supply one immutable 40-character commit, exact supported module namespace prefixes, source directory relative to repo root (empty allowed), and independently attested Git blob IDs per known module. The planner selects the longest matching namespace; exact duplicate namespace declarations are an input error. A repository binding is data, not authorization to contact it.
- `local_sources`: exact module-to-relative-path aliases and expected SHA-256 for prepared files. Hashes are checked before the import header is inspected.
- `toolchain_module_prefixes`: known compiler-provided namespace declarations. Imports matching them are recorded as unverified; they are **not** silently represented as individually located.

For a pending mapped module, use an independently authorized read-only GitHub fetch limited to the reported `repo`, `ref`, and `path`. Read its public blob metadata, verify exact source bytes, record the attested blob in config, and stage the file beneath:

    source-store/<version>/<owner>/<repo>/<commit>/<path>

Re-run from the selected target. Deeper imports can only be discovered after their importer is read. Authorization or availability problems stay pending; do not re-route, clone the entire repository, alter a pin, infer an unavailable path, or substitute a similarly named module. Unmapped, conflicting, missing, stale, unsupported, cyclic, or corrupt inputs are surfaced. Resolved paths must stay within their designated root. Input exit code 0 means the scoped declared source closure is present; 2 on incomplete closure or input error. A valid incomplete result is JSON.

## Limits and tests

- This planner reads a restricted Lean header grammar, not arbitrary Lean or Lake programs. It handles ordinary/nested comments, common header flags, import-all syntax, and implicit Init. Quoted/Unicode module identifiers are unsupported. It does not run `lakefile.lean`, infer package configuration, process package hooks, fetch toolchain or olean data, verify availability of platform plugins, handle one repository with mixed source roots, or certify module elaboration. Missing or unknown dependency tooling remains separate from package source closure.
- Dependency-first order is meaningful for the discovered acyclic source graph; it is not a build plan resolving toolchain or Lake metadata. Cycles prevent an order from being claimed.
- The Git blob hash proves staged byte equality against the independently obtained metadata, not commit authenticity or authorization by itself. The config/attestation channels must be trusted separately. The planner assumes a private, stable staging directory, not one concurrently modified by an adversary.
- Ten tests check comment/header handling, dependency order, honest unresolved toolchain status, missing attestation, unmapped import, corruption, import cycle, version isolation, path/symlink rejection, and verified local artifacts.
- The real replay reuses the already obtained nine public sources at Alexander research commit `19544a4d7608c8cc0d5a1205605c0f38631ca05f`, checking each manifest Git blob and SHA-256 before staging only the files requested. A first run asks for FullHeight only. Closure ends with nine repo modules plus two local modules (Reuse and PrefixCount); Init and Std are intentionally unresolved by the planner. Previous successful Lean checks are separate evidence from this procurement result.
