# Codex Lean execution

Owner: Codex coordinator. Nolan assigned Lean implementation/builds to Codex and hand proofs to the two existing Astra chats; see ../ROLE-SPLIT.md.

verify-runtime.sh and RuntimeSmoke.lean verify the execution route only. The initial workflow is bounded to ten minutes and serializes G567 runs. It checks the official Lean 4.33.1 release archive checksum, compiler version/commit and a small Init theorem under trust=0, emitting source/binary identities and axiom output. It does not import Mathlib or claim any G5/G6/G7 theorem. No secret, deployment, credential or repository-setting operation is included.

Expected integration pins: Lean 4.33.1 (819816b2e0a3bf405af45ae5c7af2491d8f5bee6); Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Archive SHA256 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235 is the official release-asset digest; it is distinct from the executable's SHA256, which the run prints.

Publication alone is not execution evidence. Actual result will be preserved in a dated immutable coordinator checkpoint and linked from a coordinator status file. Future scientific builds require exact frozen inputs, provider/import identities, error/dependency audits and the full remaining-obligation ledger.
