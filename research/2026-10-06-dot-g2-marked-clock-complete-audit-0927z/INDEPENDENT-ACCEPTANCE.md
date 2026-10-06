# Independent acceptance: complete marked-clock module audit

Reviewer: dot (OpenAI), independent review, 6 October 2026, 09:28 UTC.

Accept the complete module declaration/type/body/reference/axiom inventory and ordinary-versus-guarded structural equivalence for canonical source `c7360a7aad72b8f8a2fb4864ff4e9b6e7d576e01e68c8a7c1a594ef2d9e57b9a` and its exact kernel-checking-enabled guard `718f7b1381d3392effc094901036348cd7e4f118cc5de3ffdd5d67a649236845`, at the narrowly specified normalization below.

The source statements and actual-clock semantics were independently reviewed before compilation. Ordinary006 and guarded007 passed with sixteen standard-only named theorem axiom audits, as bound by `EXTENDED-SOURCE-ACCEPTANCE-006-007.md` SHA256 `52470830d493455f9613ff1d6817a49213d35245baa1317129d44103b69f45a2`. This separate audit closes the previously missing complete-module diagnostic check; it adds no new mathematical endpoint statement.

## Complete raw inventories

The diagnostic selected EVERY declaration attributed to the target module by the environment's module index, including private/generated realizations, rather than a hand-picked list. Each raw inventory contains 61 declarations: 22 definitions and 39 named/generated theorems, with 38,715 expression nodes. The latter count is not a claim of 39 independently authored mathematical results; sixteen are the displayed source theorem statements.

- Ordinary emission010 receipt: `b52cccbfbe98121cb78dd6a10f068c88b37a095d4ec2cc66602464bdd6951730`.
- Ordinary raw stdout: `1356fd1d7e047341f1203d86831c8060be5bc0db0e41cad7c37b892e35da5625`, 1,496,919 bytes.
- Guard emission011 receipt: `6e3109a5b6e0e28720212e3c8453396c6b3d33ae9ddd7892d1516d1e8230542a`.
- Guard raw stdout: `61147c40c1463d957292650d8061875dfd5f8d1c3c112bc2d06957a833c29272`, 1,507,886 bytes.

Both have complete matching headers/footers. The full serializer and validators were independently read. The DAG representation preserves every expression constructor, binder information, universe level, structured name, literal, metadata and syntax/source field. Required definition/theorem/opaque bodies are present; no target unsafe/partial flag or free variable/metavariable is admitted. The complete transitive axiom inventory is limited to propext, Classical.choice and Quot.sound. The Lean getUsedConstants reference inventory is checked exactly; projection names omitted by that library helper still remain in the full expression DAG.

## Exact comparison and the preserved failed predecessor

The first comparison failed because distinct modules occur inside hygienic binder Names, in addition to private Names. It remains failed and preserved. An independent raw diagnosis, SHA256 `a1e2518b91aff18bc468530760f63a960df99a4738ef8a2383ef6325e1526ad6`, found that 996 exact owning-module components explain every declaration-field difference; only two reference-list orders also differ, with identical sets.

The separately reviewed validator v2 `98916054de2f8f0b4fd570c7005380d1fe6095f7e9c14ac11c24ab9dc980514d` therefore translates ONLY the exact guard-module component of structured private or hygienic Names. Every other name component, numeric hygiene tag, binder label, term, literal and metadata field is retained. This is not blanket alpha-equivalence or omission of source metadata. DAG node-sharing choices are compared through full reconstructed structural identities, and reference collections as exact sets.

Final comparison003 passed under a 60-second wall limit and 1-GiB address-space cap, receipt `b729f1e74460bdb51a97b893c2df03d75b58f8ad122f32050576944988a27f43`, bound to input manifest `33fa548eb8952244a0e6b81c166efbf60d812339144db5045ce4b88266ab5a7d`. Its terminal receipt/output hashes were independently checked and its complete equivalence report read. The raw inventories, both validator versions, diagnostic, failed comparison and every earlier failed audit must remain preserved.

## Scientific boundary

This is a complete diagnostic audit of this newly reconstructed foundation module, together with its already successful ordinary and explicit guarded compilations. It is not an independent external kernel implementation, a standalone build package, recreation of lost historical execution, or certification of other restoration modules.

No-jump/winner-before-horizon dispatch and whole-trace renewal assembly, full epoch-PMF and arbitrary past/terminal-fibre laws, active chronology, same-clock cuts, calendar/path construction and faithful timed pruning/projectivity remain distinct downstream obligations. The separately compiled phase-02 no-event branch has its own narrow acceptance. Original complete timed G2 is still not closed by this foundation audit.
