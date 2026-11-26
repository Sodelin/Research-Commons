# Approved GitHub source intake

The adapter turns a bounded GitHub metadata capture into ProofBridge's existing
`{path,sha}` source-only JSONL format. It opens local JSON and writes to stdout;
it does not make network requests, resolve arbitrary URLs, clone repositories,
read Lean source bytes, run dependencies, or execute external code.

## Exact Lean 4 example

The official [Lean v4.33.1 tag](https://api.github.com/repos/leanprover/lean4/git/ref/tags/v4.33.1)
was verified to point directly to
[`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`](https://api.github.com/repos/leanprover/lean4/git/commits/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Its [root tree](https://api.github.com/repos/leanprover/lean4/git/trees/4399190c8231db0b73a116b1415e06a2591c0d57)
and the nonrecursive trees named by `src`, `src/Init`, `src/Init/Data`,
and `src/Init/Data/Nat` were captured by the GitHub connector.
Separate exact-path pinned file metadata calls corroborated the four selected
blob identifiers. Only metadata is stored in the snapshot. This is four
selected Lean core paths, not a full repository inventory, proof count,
build claim, verification of declarations, or recommended build toolchain.

## Capture and policy

1. A trusted operator explicitly approves the `owner/repo`, full immutable
   commit, matching root tree ID, exact regular `.lean` paths, and file cap.
   The adapter never converts a branch or unapproved project into a pin.
2. At that approved revision, read the GitHub Git Commit endpoint, then read
   only the nonrecursive Git Tree objects needed to trace the approved
   paths. Keep `sha,url,tree` for the commit, `sha,url,truncated,tree`
   for each tree, and `path,mode,type,sha` for every nonrecursive entry.
3. Obtain separately pinned GitHub file metadata for each authorized path;
   keep its path, blob ID and pinned display URL. Do not retain source text
   in the capture. Untrusted comments, filenames and metadata never become
   instructions.
4. The adapter checks the approved root identity and recomputes every
   serialized Git tree ID (including nonselected children needed for each
   tree hash). It validates parent-to-child links, rejects truncation, path
   escapes, unapproved branches, symlinks and submodules in the selected
   chain, and requires agreement of separately fetched path metadata.
   No unreferenced tree object may be carried in the input capture.

The trusted allowlist attests the commit-to-root link as observed at the
official endpoint; the adapter independently recomputes tree IDs from
captured metadata, not the commit hash or any source blob hash. A consumer
checking only a generated digest gets consistency, not authority to
install or replay that provider.

## Replay

From this directory:

```sh
python project_intake.py --provider lean4_core_selected --allowlist reference/approved.json --capture reference/lean4-core-capture.json --format rows
python project_intake.py --provider lean4_core_selected --allowlist reference/approved.json --capture reference/lean4-core-capture.json --format providers
python project_intake.py --provider lean4_core_selected --allowlist reference/approved.json --capture reference/lean4-core-capture.json --format receipt
PYTHONDONTWRITEBYTECODE=1 python -m unittest -v
```

Exact results are preserved under `generated/`. A configuration-driven
federated search reader can merge `providers.fragment.json` into its
provider table and map the unchanged path/blob shard to the
`lean4_core_selected` key. Its layer stays `external_source_only`.
Verify receipt schema, matching repository/revision/root/provider fields,
digest, row count, and source-only flags before reading the new shard.
