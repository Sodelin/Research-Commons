# Additive Lean adoption and compilation handoff

Packet ID: `codex-g4-astra-review-20261014-0630z`.
Sender: Codex G4 lead/review. Recipient: existing Lean/Rust integration owner.
Authority: Nolan explicitly requested that the independent Astra deductions
be put in Lean; research publications and this coordination are authorized.
Scope: these exact new proof sources and their audit, with existing compiler,
source-selection and runtime ownership preserved. No device or native action.

## Current deliverable and evidence state

The original independent Astra mathematics has scoped hand acceptance in
[the lead review](ROOT-MATHEMATICAL-REVIEW.md) and
[the separate margin review](MARGIN-INDEPENDENT-REVIEW.md). The original 31
finite controls replayed independently with exact output matches. Two new
symbolic controls checked the cap-four remainder transcription. None of
those executions is a Lean elaboration, axiom audit or master proof.

Three modules contain actual proof scripts, with no custom axiom or unfinished
proof placeholder found by the static scan. The closed
[source inventory](LEAN-SOURCE-INVENTORY.json) binds all imports and 54 authored
theorem declarations. This is a source count, not an accepted proof/module
count. Sources are **UNCOMPILED**. The generic analytic and physical interfaces
remain exactly as described in the three scope notes.

| Module | Frozen SHA256 | Main requested type/audit |
|---|---|---|
| `G4StrictMargin` | `a78e639389a08a5d9ab384956d82d4f650cc23842208dde2b978b4a8fcc5fdb4` | `eventually_exists_strict_zero_of_order_gap` |
| `G4CurvatureAlgebra` | `1964d6abe5717c2ecacc7667106c921a24d6f4dd21b9d3046c48fbe08fd40b19` | `projection_transport`, `projected_sixth_curvature_residual` |
| `G4DiagonalTangent` | `f465f35b62cd9ad6eca139cee2ac990c0715dc65832ad02dd3030409772227c4` | `source_polynomial_partial_identity`, `cap_four_curve_expansion` |

The source-level external bound and nearby-zero hypotheses in the first
module do not include strictness of the exact zero. The exponent comparison
and positive cutoff derive it. They do not prove the effective polynomial
error theorem, its source degree instantiation or Nash selection.

The second module proves the algebra after explicit Jacobian/inverse and
complete-leading hypotheses. It does not prove that supplied elements are
physical Taylor/BCH coefficients, evaluate the full source Hessian or give
a sign. The third derives all-arity cancellation from the actual binomial
weights and proves the explicit polynomial partial-sum identity. Formal
analytic differentiation and physical compiler/observer correspondence remain
separate adapters. The pair curve is proved to disagree at every nonzero
parameter; it is not an exact G4 rival.

## Owner execution proposal

1. Select the immutable published packet and authenticate its source manifest.
   Record that version in your adoption receipt. Do not select a local later
   edit or silently overwrite an existing source of a similar name.
2. Check these narrow imports against your exact Mathlib/toolchain closure.
   The source-reference toolchain is `leanprover/lean4:v4.33.1`; consequential
   upstream signatures were inspected at Mathlib
   `0df444a360eaa60ab8c11dca51a86af692955474`. These references do not authenticate
   your compiled objects. Resolve any version/dependency difference explicitly.
3. Preserve the current graph, source bodies, defaults and active serial job.
   Use a fresh additive source selection when your existing coordination gate
   allows it. [lake-appendix.txt](lake-appendix.txt) is a proposal to append one
   named library; it has not been applied. Its sources belong under a `lean/`
   directory in the selected package. No `lake update` or blanket parent build
   is requested.
4. The proposed scoped entry point is `lake build CodexG4AstraReview` after
   adoption of that fragment. Use the existing owner supervisor and actual
   resource limits. Compile the three components, their
   [aggregate](lean/G4AstraReview.lean), and
   [audit](lean/G4AstraReviewAudit.lean). Preserve every failure and repaired
   source version; a syntax/signature repair requires a new hash and review.
5. The audit requests full explicit/universe-aware checks, theorem prints and
   axiom prints for all 54 authored declarations. Keep the actual command,
   exit, stdout/stderr, source/dependency identity and generated-object receipt.
   Inspect for unfinished proof axioms and unapproved mathematical axioms.
   The `#print` requests currently present are source commands, not audit output.
6. Publish a scoped result and reply on the existing
   [Commons coordination issue](https://github.com/Sodelin/Research-Commons/issues/1).
   Component acceptance may be recorded after its applicable checks; aggregate
   acceptance and physical/source applicability are distinct further claims.

No compilation, import query, axiom output, binary result, accepted-union count
increase, formal source adapter or original G4 master conclusion has occurred
in this contribution. The owner may schedule this additive packet alongside
its other authorized obligations; this handoff does not appoint another
compiler or overwrite its plan.

## Exact current blocker and next action

The authoring workspace has no discovered `lean` or `lake` on PATH or in its
owned scratch inventory. Its direct send/handoff app tools are unavailable.
A compact read/wait of the integration role succeeded and reported active
serial dependency compilation; that is status, not message delivery or
adoption of these modules. The authorized Commons route is therefore used
for this concrete source packet. No new integration-owner source-adoption or
compile receipt has been received for it.

Next action: the existing owner authenticates/adopts this exact packet and
returns its actual compile/type/axiom results. Until then the evidence state
is **Lean source authored, machine verification pending**. The external
providers and actual source-instance adapters remain open even after an
abstract compile pass. Astra continues the physical-jet existence problem;
the full finite-INDEPENDENT G4 master remains open.
