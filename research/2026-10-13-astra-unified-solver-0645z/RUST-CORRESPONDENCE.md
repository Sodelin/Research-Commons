# Exact certificate slice and native correspondence

This addition checks a bounded language of supplied rational COMMON certificates.
It does not recognize arbitrary sources, acquire every needed certificate, or
implement the missing physical representative construction. All source existence
and exclusion decisions remain with the existing admitted-source backend and its
own contracts. A successful arithmetic check alone is never a source YES.

## Exact accepted language

`certificates.py` accepts the versioned `common_sparse_certificate_v1` JSON
object with exactly `schema`, `level`, `coefficients`, `moments`, and
`nonnegative_terms`. Let `L=level`, `e_k=k(k-1)/2`, and
`p(x)=sum(k=1..L, c_k*x^e_k)`. It checks:

* `1 <= L <= 8`, exactly `L` coefficients and moments, and at least one nonzero
  coefficient; all moments lie in `[0,1]`, with first moment exactly one.
* Each of 1–16 supplied square terms is `w*x^left*(1-x)^right*q(x)^2`, where
  `w>=0`, `left,right` are each 0 or 1, and `q` has 1–15 coefficients in ascending
  degree order. Exact polynomial expansion must equal `p` coefficient by
  coefficient. This implies nonnegativity on `[0,1]`; this certificate language
  is not claimed complete for all real nonnegative polynomials.
* The exact rational sum `sum c_k*y_k` is zero. Checking this arithmetic does not
  establish that the supplied moments come from an actual source.

Rational transport tokens are ASCII signed integers or `p/q` with positive
unsigned denominator, at most 80 bytes and at most 128 bits in the numerator's
absolute value and denominator **after reduction**. No plus sign, leading zeros
other than zero itself, decimal/exponent notation, Unicode digits, or floats are
accepted. `-0` and reducible fractions such as `2/4` are accepted exact values;
the spelling of a rational is not a unique certificate identity. The exact JSON
object is hashed, so changing its spelling changes its certificate identity.

The JSON loader rejects duplicate keys, floats, nonfinite numbers, malformed
encoding, requests larger than 256 KiB in encoded bytes, and nesting beyond 64
levels. The Rust executable consumes a separate bounded ASCII wire with the
same arithmetic fields, not JSON or external source IDs. It accepts ASCII
whitespace between tokens, rejects trailing tokens, and reads at most 256 KiB
plus one byte to detect size overflow. Wire natural numbers have canonical
unsigned decimal spelling and explicit caps. Successful output is exactly
`CHECKED_RATIONAL_CERTIFICATE support_cap=N source_existence=false`; refusal
exits 1 with a `REFUSED` reason and no successful output.

`generate_singleton` is a bounded data-driven acquisition method for precisely
the three supplied moments `(1,a,a^3)`, `0<a<=1`. It emits
`p(x)=2*a^3-3*a^2*x+x^3=2*a*(x-a)^2+x*(x-a)^2` and runs the same checker. It never
queries an unknown target or invents a missing observed moment. Failure to fit
this sufficient rule or to fit the output transport caps returns `UNKNOWN`.

The `supplied_common_menu_v1` wrapper uses one fixed list of 4–8 taxon IDs,
protected edge/hybrid ID lists, a joint configuration PMF, and exactly one
certificate per ordered taxon pair (including diagonal). It requires exact
total mass one, preserves complete joint masks, and records positive-mass
configurations without renormalization. Protected masks must mention every
protected hybrid ID; duplicate or unknown IDs and unsupported nonempty
parameter constraints are refused. It computes the conditional arithmetic
budget using `h = |PE|+|PH|` and `S=max(L_ij-1)`. The result remains `UNKNOWN` and
the budget is **not applied to source search**: fixed external copy/readout,
all protected dependencies, parameter admission, actual moment binding, and
the physical representative theorem still need the named provider/bridge.

## Reused implementations and semantic links

Rust uses the existing `exact-count-certificate` library from
`research/2026-10-07-rust-count-pilot` as a path dependency for `Rational` and its
established exact parser. The new wire imposes its narrower syntax before
calling that parser. `num-bigint=0.4.6`, `num-rational=0.4.2`, and
`num-traits=0.2.19` perform exact integer/rational arithmetic. No floating-point
operations or approximate certificates occur in this slice. The existing count
pilot's Poisson/count-budget output is not reinterpreted as a hybrid bound.

| Mathematical item | Executable item | Correspondence and remaining boundary |
| --- | --- | --- |
| `Astra.CommonCertificateKernel.squareTerm_nonnegative` | Exact expansion of a weighted square with endpoint factors | Same term semantics; no verified extraction or parser refinement. |
| `square_identity_nonnegative` | Exact equality of expanded rational coefficient arrays | Equality over rationals embeds into equality over reals; the array arithmetic implementation is trusted/tested, not formally refined. |
| `supported_atom_is_root`, `joint_supported_bank_is_root` | Zero exact annihilation; full joint configuration and positive support retained | Lean requires the actual finite-bank identity, positive bank weights, and survival range. The program does not manufacture those source premises. Zero configuration mass forces no root. |
| `singleton_generator_identity`, `singleton_generator_annihilates`, `singleton_generator_nonzero` | Deterministic three-moment generator | Exact same cubic formula; float fitting is absent. |
| Selected1613 `G4ActualPositiveGridUniqueness.positiveCertificateGrid_card_lt` and `G4WholeProfileDetermination.finiteBank_certificate_restricts` | Report `L-1` as a conditional positive-support cardinality cap | Earlier selected provider scope is inherited; the new semantic kernel does not reprove the sparse root-cardinality theorem or validate actual-source admission. |
| Missing physical `G4ProtectedCommonRepresentative` and uncompiled `G3CertifiedCommonBoundedWitness` composition | Menu output remains `UNKNOWN` | No axiom or desired conclusion replaces the physical/admission/encoding bridge. |

The survival domain is `(0,1]`: endpoint one is allowed, endpoint zero is not.
The arithmetic checker can accept `p(x)=x`, moments `(1,0)`, since those form a
valid nonnegative zero-expectation certificate. That success does not assert an
actual `(0,1]` distribution exists; the explicit regression test prevents that
interpretation. Source feasibility requires a separate actual-source check.

The prior canonical snapshot decoder and serial full-history controls were
inspected through their exact source/receipt packets before this addition.
They have separate semantics: native snapshot witnesses do not supply unique
history recovery, and identical interned final states do not imply identical
serial histories. This narrow checker neither replaces those interfaces nor
silently claims their unavailable core has been compiled here. Any recovered
core must match its frozen dependency identities before integration.

**Recovery update, 07:04 UTC:** that identity check has now succeeded against
an existing immutable public branch, and the recovered core, latest decoder,
serial full-history controls, and existing population controls were freshly
compiled and executed. See [RECOVERED-PARITY.md](RECOVERED-PARITY.md) for all 25
matched historical pins, the complete 51-file source inventory, exact relocation
of the serial harness's module path, preserved failures/repairs and actual
receipts. This supersedes the executor-local core-availability gap above.

## Verification and trusted boundaries

`test_certificates.py` checks a deterministic rational corpus, certificate
mutations, exact parser limits, malformed JSON, acquisition exhaustion, fixed
joint PMF/ID handling, and refusal of unsupported constraints. `test_native.py`
feeds the same exact certificates and deliberate wire mutations through the
compiled executable, requiring exact output and exit-code agreement. Rust unit
tests additionally exercise the narrow parser, caps, endpoint one and the
non-source zero-endpoint arithmetic example.

The initial Python run is preserved in `evidence/python-certificates-first`:
six groups passed and the deep-JSON test failed because this host accepted
2,000 nesting levels. The repair adds an explicit depth-64 check independent of
the interpreter recursion setting. `evidence/python-certificates-depth-repair`
records seven passing groups after the repair. The fresh Rust checker passed
five unit groups; its process differential run passed all 556 cases (180
accepted, 376 refused), including 178 generated exact certificate forms.
Execution receipts state limits,
exit status, pressure samples, peak child RSS, elapsed time, and output hashes.

The finite tests do not prove universal native-code correctness. Remaining
trusted boundaries include the Python interpreter/Fraction/JSON/SHA-256
implementations, Rust compiler/standard library, exact arithmetic crates,
transport-to-mathematics correspondence, theorem-to-executable selection,
actual source/observation encoding, and OS/process execution. Lean kernel
checking proves only the displayed formal semantic theorems under their exact
assumptions; it is not a verified compiler for this Python/Rust implementation.
