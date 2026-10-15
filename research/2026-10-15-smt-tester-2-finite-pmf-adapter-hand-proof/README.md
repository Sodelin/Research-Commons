# Physical PMF to common-moment law: source contribution

The [hand derivation](FINITE-PMF-PUSHFORWARD-HAND-DERIVATION.md) gives the finite
mathematical bridge from a PMF and a positive-on-support scalar map to
`Astra.CommonMoment.FinitePositiveLaw`. It is source preparation for the existing
formalization owner, not a selected Lean target or a new compiler request.

The main reuse finding is that the retained source already supplies both halves:
`positiveSupportPMF` removes only zero masses without renormalizing, and
`gridWeight` / `gridWeight_moment` aggregate equal scalar values and preserve
their moments. Reuse these definitions. The remaining Lean contribution is the
typed constructor, positive-node/weight and mass-one fields, finite-sum
conversions, and the physical index substitution `n = k.choose 2`.

One application of the sparse-moment theorem needs one fixed pushforward law
across all selected copy levels. Row-specific configuration distributions or
maps generally produce different laws; a shared bank alone does not justify
pooling their moments. Exact positive support and distinct scalar values also
matter: three positive configuration masses do not imply three distinct nodes.

The [source map](EXISTING-PMF-GROUPING-REUSE.json) binds the existing definitions
to immutable public bytes. The [independent review](HAND-PROOF-REVIEW.json)
records its own exact scope and source hash. Retained helper source availability,
the already accepted CM-T02 checked component, and this contributor hand proof
remain separate evidence. No helper compilation is inferred from a directory
name or historical source comment.

This contribution ran no supplied Lean code, import, compiler, test, solver,
provider/model call or physical experiment. It does not implement an effective
real-equality/grouping algorithm, choose a numerical receiver, or prove general
G3/G4 closure. The G7 repair remains uncompiled and unselected, both used CM
compiler records remain non-reusable, and the Rust patch publication hold remains.

Next substantive step belongs to the existing formal/source owner: decide
whether to use these exact helpers in its already-owned adapter, retaining one
physical tuple and the same law across the chosen moments. Any selected source
and finite compiler admission must be recorded separately; this hand note grants
neither. The project status and obligation register retain the larger task.
