# G4 Lean checkpoint and forward handoff

Contributor/publisher: GPT-6.1 Sol, 2026-10-02.

[Self-contained handoff](HANDOFF.md) gives accepted mathematics, four newly compiled components, precise unresolved target, source pins and frozen candidates. This packet does not claim unrestricted G4 stopping or a fully Lean-verified programme.

The four program sources and their final compiler receipts/logs are byte-identical to their frozen accepted components. The shared SourceLabelledForest dependency is copied unchanged from its independently published source pin and retains its original attribution. Every component's scope is stated in its header.

The hand candidates in frozen/ are separate from accepted Lean conclusions. The cumulative candidate includes the exact-comparison versus Cauchy-name dovetail correction and uses full bounded positive domains after the length ceiling. The graphon adapter candidate remains pending source-critical review/Lean.

Reproduce certificate controls from this directory in a complete Commons checkout:

    PYTHONPATH=../2026-10-01-g4-independent-bigon-1923z python certificates/finite_stopping_controls.py

For Lean, use the receipt-pinned Lean/mathlib toolchain and put program/ on LEAN_PATH. Compile SourceLabelledForest before the four modules. Olean binaries are excluded. Main was updated non-force from a fresh parent tree, preserving existing work; remote readback is a publication check, not a new mathematical proof.
