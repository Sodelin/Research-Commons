# Explicit original bank ordering

`NativeOrderedBankLayout.lean` constructs the exact coordinate order already
used by the original native cell compiler. The caller supplies the vertex,
edge and original-hybrid occurrence equivalences. The construction returns
one bijection from `V ⊕ (Option E ⊕ H)` to `Fin (nv+ne+1+nh)`.

| Original variable | Native position |
| --- | --- |
| Vertex age `v` | `vertices(v).val` |
| Edge inverse rate `some e` | `nv + edges(e).val` |
| Ancestral inverse rate `none` | `nv + ne` |
| Hybrid parameter `h` | `nv + ne + 1 + hybrids(h).val` |

`Astra.NativeOrderedBankLayout.ordered_bank_positions` proves all four
identities and that the ancestral slot has exactly the `none` preimage.
Its supplied equivalences retain every coordinate; no dimension reduction,
source acquisition or parent-order interpretation is assumed.

Actual hosted checking selected `bankEquiv` and `ordered_bank_positions`.
Both complete types and axiom lists are retained in `CHECKED-FOLLOWONS.json`.
The check had no errors or warnings, no `sorry` and no additional axioms:
the selected dependencies are `propext`, `Classical.choice`, `Quot.sound`.
Context: Lean4.35.0/mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
manifest SHA2563bafb347b291b221e474e7c02b2390a921c7be64ec272c300699c46eab37a270.

Exact standalone source:3655 bytes, SHA256
00d0b83e92f5d182b25f590b005f6ef95879f79f5adba18b6997e20b33b4e51a.
The submitted source adds only the recorded audit-command suffix, SHA256
86c49a5bdd7dfd3395638049a2d0e715cc7cada8d1cdd727d1e404548b6edb08.
The used Fin equivalence definitions and simplification lemmas were also
located in the separate pinned mathlib0df444 source. That source reading
does not establish native import or object acceptance.

`OriginalCodeBankLayout.lean` is the original-Code use-site of this construction.
It reuses the existing `sourceOfValid`, `decodedIDs`, `decodedRegistry` and
`decoded_parent_exact`. For the literal finite Code, vertex and edge numbers
are identities; hybrid coordinates use the supplied original-ID order through
`decodedIDs.symm`. It retains explicit `BinaryValid` and `RegistryValid`
premises. The revised source removes one unnecessary affine import and spells
the same bank sum type directly:2726 bytes, SHA256
9a8cb5634c358627aee56339206e97c1f2c0c2c2b393bdd4151a041a88366208.
It now passes a complete hosted admission-component check, including the entire
43-original-module dependency closure and two explicit hosted API variants.
ADMISSION-COMPONENT.md gives the six selected full types/axioms and exact scope.
The older2733B/ef18d6a1 source remains immutable in parent history. The wrapper
has NOT been elaborated in its pinned full native import context.

Both files join the source-only physical/PMF/CM context. The layout snapshot
had543 modules/4,504,069 bytes; the later CHART form-reflection addition gives
545 modules/4,518,048 bytes. This latest wrapper-only revision gives
545 modules/4,518,041 bytes; all other544 entries are unchanged. The graph keeps
both literal bank witnesses and the Code-layout use-site as roots. Full-import
elaboration, native Lake, compiler and object custody remain unrun under the
actual first-writer hold.

The next binding is exact captured native arrays to this literal Code,
admission proofs and complete original registries, then exact ordered row
emission into `compileCell`. The existing M0 incoming-port correspondence,
inverse-rate positivity, source class/menu and physical/readout semantics
remain explicit premises. The generic layout proof supplies none of those
additional relations, and cannot turn a finite matrix exclusion into source NO.
