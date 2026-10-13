# Static source review and compilation handoff

This is the integration author's static mathematical and interface review of
the new source candidate. It is neither independent hand acceptance nor a Lean
execution receipt. The two `#print axioms` commands have not run.

The exact selected upstream body is `G4WholeProfileDetermination`, SHA256
`fb4b6ba74553b4ec4d93204dd38a3632227a51577aee087de4ae17758c63fe09`,
from accepted public 1613 commit
`7239e89dea5caad68a54227cee3b44a7d9b96389`. Its historical source header still
says working/uncompiled; selection is established by the pinned later accepted
packet, not by rewriting that header or claiming a fresh compilation now.
The [dependency delta](DEPENDENCY-DELTA.json) pins this and every newly selected
body through the immutable selected graph. The whole original module is used.

The proposed chain is:

1. `momentLevels_positive` in selected `G4ActualSparseCertificateExistence`
   gives positive queried levels. `actual_randomized_legal_moment`, lines
   3529–3539 of the selected whole-profile source, identifies each actual
   normalized legal row with a joint-bank moment.
2. `finiteBankMoment` uses exponents `k.choose 2`, not `k` or consecutive
   polynomial degrees. `finiteBankMoment_polynomial`, lines 2779–2789,
   distributes the supplied finite coefficient sum through the finite bank.
   Substituting the exact row matches into the supplied zero scalar identity
   proves `actual_rows_certificate_annihilates`.
3. Joint weights are ENNReal PMF values converted to real, hence nonnegative.
   `directedSurvival_bounds`, lines 2873–2876, proves every tree value lies in
   `(0,1]`. The new wrapper obtains these domain facts from the selected source.
4. The staged `Astra.PositiveSupportAdapter.supplied_certificate_support_bound`
   uses polynomial nonnegativity, zero expectation and a nonzero evaluation to
   derive the root condition and then the `L−1` bound. The new theorem does not
   take roots, support/cardinality bounds or a physical representative as input.

`momentLevels L` is exactly `1,...,L`; the exponents are `0,1,3,6,...`.
The adapter counts distinct values with strictly positive real weight, not
configurations or multiplicity. Equal survivals count once; zero-weight
configurations do not count; the value 1 is retained. `L=0` is excluded by the
nonzero-evaluation premise, rather than by assuming the desired bound. The
selected actual-row theorem does not require `i ≠ j`, and no such restriction
is added. Coinciding ordered endpoints, when used, give the corresponding
selected row and survival rather than an invented observable.

The encoding is the imported definition itself: `randomizedLegalCombMoment`
uses `paddedSample k i j`, pruning by `paddedKeep k`, the singleton unranked comb
rooted at `paddedB` with the `paddedA` list, and division by `combCoefficient k`.
The padding contains `k` copies at taxon `i`, one at `j`, and one extra copy per
original taxon; only the first `k+1` copies remain after pruning. No i/j reversal,
change to the comb event, or replacement normalization is introduced. This
composition does not prove the Rust parser emits that exact row.

The quantifiers fix `N,C,H,p,r,ν,masks,i,j,L,coeff,moments` before all queried
levels. `configurationBankPMF ν (originalRegisterMeasure N p).toPMF` draws one
whole mask configuration and one independent natural register bank. It preserves
correlations within `ν`; it does not license replacing them by products of
site marginals or introducing arbitrary configuration/register correlation.
The original types `V,E,X`, edge instances, parent registry and original masks
are retained. Neither proof rewrites IDs or protected dependencies.

Physical admission is precisely the imported interface: finite `RootedBinary`,
its calendar, original parent registry, hybrid probabilities and positive pair
rates. `RootedBinary` alone deliberately does not assert planarity or cut-child
geometry. Additional original-branch or protected-ID conditions can be imposed
on these same inputs by a later consumer, but this wrapper neither assumes
their conclusion nor proves preservation under a source replacement. No target
existence is inferred from a certificate: the theorem holds for every compatible
realizer, including vacuously when no such realizer exists.

This does not supply the missing exact `G4ProtectedCommonRepresentative` body
at SHA256 `0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04`.
It proves neither a physical bounded COMMON representative nor its existence
before all future rows, no hybrid bound, and no G3 YES/NO decision. The 19:38
calibrated original-source hand theorem remains a separate prose integration
obligation; an ordinary `NoHybrids` result is not substituted for it.

The source has two theorem proofs and two definitions. Static inspection finds
no axiom, `sorry`, `admit`, `sorryAx`, native decision tactic, or placeholder.
The remaining trusted formal boundary includes elaboration/typeclass resolution,
the complete selected upstream proofs, the staged support adapter, and the
actual transitive axiom audit. Only a real compiler run can discharge that
boundary; passing this review is not a compile result.

For the sole build/publication owner:

- Preserve the ongoing 319-owned/3591-external plan. The distinct proposed
  whole-profile closure contains 469 selected owned bodies, adding 148 research
  bodies and two Mathlib bodies. All 469 source identities and literal imports
  were reauthenticated without compiling.
- The added Mathlib `MvPolynomial.Funext` and `.Polynomial` bodies are identical
  to both the selected Commons sources and the remote exact Mathlib revision
  `0df444a360eaa60ab8c11dca51a86af692955474`. Their official compiler import
  queries and the complete expanded build plan remain pending. All additional
  direct non-toolchain roots already occur in the current external plan;
  `Lean.Elab.Tactic.Omega` belongs to the pinned compiler.
- Once the current adapter closes, materialize the complete selected dependency
  graph in a separate successor build configuration. Resolve any ownership
  overlaps explicitly, preserving full selected bodies and current source pins.
- The supplied aggregate entry is `lean/AstraLegalRowSupport.lean`; no Lake
  target for it is configured yet. Add its target under the owner's normal
  source authentication and serial resource guards, then compile the new wrapper
  and aggregate, retain logs and run both new axiom-print commands.
- Record fresh compilation separately from authenticated object reuse and
  publish source/configuration/receipts by non-force update with remote readback.
  Until then this packet is a source handoff, not a reproducibly delivered proof.
