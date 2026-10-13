# Native supplied-certificate acquisition

The existing Rust checker now generates and checks a singleton certificate
from supplied moments `(1,a,a^3)`, `0<a<=1`. It reuses the exact parser,
checker and arithmetic dependencies. Unsupported moments or derived coefficient
limits return UNKNOWN; malformed input is refused. No unknown target, extra
observation or floating-point optimizer is supplied.

Implementation remains in the unified packet's `rust/src/main.rs`. See its
[exact contract and reproduction](../2026-10-13-astra-unified-solver-0645z/NATIVE-GENERATOR.md).
Invoke `solve.py` with a `generate_singleton` request,
`--rust-binary /path/to/new/common-certificate-checker --native-generation`.
The flag requires exact Python/native generation agreement. The original route
remains available without it; missing native capability yields UNKNOWN.

Verified results:

* Eight Rust unit groups, 158 acquisition cases (125 generated, eight UNKNOWN,
  25 malformed refusals), and 556 existing checker regressions pass. All generated
  certificates pass both the preserved old checker and the new checker.
* `evidence/unified-cases` and its resource receipt preserve 19 end-to-end cases
  with native generation enabled. Two old-binary compatibility cases also pass.
* `evidence/SUCCESSOR-CORRESPONDENCE.json` checks current source pins, native
  generation agreement and exact emitted-proof identity against the earlier
  successful Lean execution. This is authenticated reuse, not a new Lean build.

New binary SHA-256:
`3d7678fac5ba8138b28a08e40c6ca8ac2b3a6e13267350d48480997e53f27ef7`.
The old binary is untouched. Builds were serial, offline and guarded.
The [immutable Lean baseline](https://github.com/Sodelin/Research-Commons/tree/9031b31be9d831199b5e8ccedcf98045df82d720/research/2026-10-13-astra-unified-solver-0645z)
retains its manifest, also archived in `baseline/` here.

The eight-file G4 successor is indexed in `intake/`, with reviewed spectral
results separated from the pending partial-program candidate. The missing
physical provider, uncompiled combined `AstraUnified`, general acquisition and
native refinement obligations remain explicit. Finite tests do not prove
universal native correctness or arbitrary-input G3 closure.

Verify this manifest with the unified `verify_packet.py --root
research/2026-10-13-astra-native-acquisition-0815z`. Research Commons issue1 and
`communications/` retain intermediate milestones, failures and delivery links.
