# Actual portable package verification

Initial source8e9b13157901d9ba2952075c3ad5a9f3b2cb8a82 was checked by [hosted run39940552120](https://github.com/Sodelin/Research-Commons/actions/runs/39940552120), job120370631442, on Ubuntu24.04/Rust1.90. This is a new portable public-source build, not execution on the phone or reuse of a historical native permit.

The build reached the retained G7 library and failed with rustc E0023 at line1349: `Formula::Exists(_)` matches one field although `Exists(Vec<Symbol>,FormulaId)` has two. The portable copy uses `Formula::Exists(..)`. The original PR2 source remains unchanged; source-lock.json names the exact original and one-line variant. No test PASS or Lean build is claimed from that failed run. The Lean and completeness jobs were skipped because the Rust job failed. The actual failure and source history are retained.

The full registry integration gate remains incomplete, independently of this compiler repair. A code-only PASS is not full93-claim formalization or original G3/G4 scientific closure.

The portable full-profile builder additionally reuses the retained complete ownership/axiom audit template. It checks every selected module plus the new package/registry modules, refuses owned axioms/nonstandard axiom rows/missing modules, and keeps the full audit as a separate hosted artifact. Ordinary warnings are not conflated with untrusted axioms; actual audit failure remains fatal. This new build is not a transfer of the original compiler/object-custody receipt.

Run39941173600 (source2576969232349d2157bca5101be75576b823d373) passed the retained G7 compilation point but stopped on a mismatched delimiter in this package's new runtime test fixture. The fixture was corrected without changing the problem or expected outcomes. Its actual Cargo.lock was recovered from the marked log block, checked against the run's printed SHA256 and committed; subsequent Cargo calls use --locked. Hosted checkout is narrowed to this self-contained package. No Lean PASS or full claim-integration PASS is inferred from that run.
