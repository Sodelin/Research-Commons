# Phone/Termux solver port and tool interface handoff

- ID: 20261010T140035Z-phone-termux-solver
- UTC: 2026-10-10T14:00:35.224126+00:00
- Contributor/publisher: Codex / phone-termux session; two delegated Codex agents supplied practical exploration, native verification and independent review.
- Intended readers: practical-solver and molecular application maintainers, dot, and the separate practical-build agent.
- Kind: tested-result update and workflow question.
- State: directly observed phone tests; proposed follow-up; acknowledgement not received.
- Source checkout: [`2d5c7742413aa14a8cc46cdc70a8b0a009b85e7e`](https://github.com/Sodelin/Research-Commons/tree/2d5c7742413aa14a8cc46cdc70a8b0a009b85e7e).

## Request and current result

The user asked whether the existing Rust/solver work could run through Android Termux and be shown in a simple local browser interface, and requested coordination through Commons. The phone port now runs the included practical solver examples, with its independent journal checker and an Android-built optional Rust diagnostic. A browser page displays the nine exact-result-derived widths and distinguishes conditional narrow bounds, finite-data UNKNOWN and refusal, with original HTML/Markdown/JSON evidence available locally.

The actual application core is Python; Rust is an optional signed-nine pair diagnostic. Its successful Android build is useful compatibility evidence, not a measured producer speedup.

| Included example | Observed scoped status | Producer launched | Checker launched | Native diagnostic |
|---|---|---|---|---|
| Informative | CONDITIONAL_UNION_WIDTH_CERTIFIED | True | True | COMPATIBILITY_PASS |
| Finite data | UNKNOWN_OUTER_COVER | True | True | COMPATIBILITY_PASS |
| Unsupported | MODEL_NOT_ADMITTED | False | False | not invoked |

The informative example's maximum normalized whole-union width was 0.0037718044494779073, below its 1/20 target. A separately launched independent recheck returned `CONDITIONAL_UNION_WIDTH_CERTIFIED`. The finite-data example retained its intended UNKNOWN rather than claiming sufficient information. The unsupported request launched no producer/checker.

## Android portability details — tested result

Native Termux Rust 1.99.0 compiled the recovered locked signed-nine-probe source for aarch64-linux-android. Existing source/lockfile bytes were preserved. The inherited comparator's 256 MiB virtual-address cap aborted Android startup; the original failure was retained. A separate Android resource adapter matched all 39 exact fixtures (13 completed geometries, 26 refusals), nine transport controls and the 97-row limit control. The interval core passed 10 tests. The separate molecular Rust core passed 18 unit and three CLI tests.

The practical launcher's original 512 MiB virtual-address cap also aborted Python before computation. Even a tiny Python process reserved about 10 GiB of virtual address space while using about 12 MiB resident RAM. That was usage, not a phone-wide RAM cap. Tested Python producer/checker resident peaks in the successful runs were about 24–27 MiB.

The phone adapter uses a 16 GiB virtual-address ceiling and samples each directly supervised child's resident memory against 512 MiB every 50 ms, retaining the practical launcher's 30-second CPU, 45-second wall and 16 MiB per-file caps. The separate native fixture adapter retains 15-second CPU/30-second wall caps and samples a 512 MiB resident guard every 5 ms. Sampling is not a hard process-tree memory ceiling. Applied nested native limit overrides are persisted from the preexec fork and embedded in the parent result; inherited nested receipts retain the desktop limit they requested.

Android Python lacks os.link, and libc hard-link creation was denied on this platform. Only journal publication was adapted: a file fsync followed by renameat2(RENAME_NOREPLACE) replaces hard-link-then-unlink. Atomic publication and existing-target refusal were tested. Canonical journal content, hooks/state updates, numerical source bytes, request checks and the independent replay remain preserved. Port results are explicitly labeled FRESH_TERMUX_PORT_RUN with the upstream execution mode retained. Saved evidence remains SAVED_RESULTS and launches no solver.

## Evidence identities and review

Full runtime artifacts, failed attempts, source versions, receipts and the browser interface are preserved on the phone. The executed adapter versions are archived by hash; subsequent saved-report labeling refinement has its own source version.

- Preserved upstream launcher SHA256: `038806682634b11db85179270304f0ea78e88c14230d83ba3e4703fa52a1be88`.
- Informative request SHA256: `81de438bcffe5f80a7ca3fa997365b1ecf6996a3171f81a0067f58acfe428e1f`.
- Native binary SHA256: `d76ce8560e1113a4a65463ecbf09ea795294a26f53ff0a35880773eb6ac3f8ba`.
- Executed practical phone adapter SHA256: `badad7ca3c935288497f2919c9fb05d7102f3b6d55722dda9784649a54c6c85c`.
- Executed child bootstrap SHA256: `9dffa4a9b4809927e5293e435c42fb3f525429d7bc30e1128c9e84fb35cbd9a9`.
- Informative result SHA256: `876a5ee047cfedd2b99ac8c560143d0d154f1beb88cbaad4f4f853f5d50b859e`.
- Finite-data result SHA256: `e865361d7dfd523f303cd88f2150361f1652f9b1ec3f321e1ffe566515c57d48`.
- Native fixture verification summary SHA256: `9b5e6b0257f81aad2716d060f0de271c938e5fcc575828a5989eef28d92fa280`.

A delegated reviewer checked 50 informative and 84 finite-data artifact identities, source/bootstrap identities, equality with complete checker output, exact width fields, native comparison results and journal publication semantics. The browser endpoints and display logic were exercised; no actual Firefox debugging connection or visual screenshot inspection is claimed.

The finite fixture tests and conditional widths establish scoped software compatibility. They do not establish biological accuracy, source existence, statistical confidence, universal arithmetic equivalence or original G3/G4 closure. No Lean build, live genome service call or credential activation occurred.

## Questions and practical next actions

1. Which existing request/data workflow should the phone UI support next, and which real input needs an admitted mapping before it can reach the practical solver? Please link the canonical contract and an appropriate nonprivate fixture.
2. Is there another intended Rust solver core beyond the signed-nine diagnostic and molecular haplotype core that this phone session should port?
3. For the documented AlphaGenome integration, please identify the current reviewed access/provider contract and an official API setup entry point. User interest in phone API access is exploratory; keys must remain outside Commons and chat.

Other proposed phone tools are an offline FFmpeg converter (WAV-to-MP3 and SRT-to-VTT conversion already tested), a readable output shelf, and a small local assistant that selects predefined tools. These are interface directions, not new scientific claims or completed model installations.

Next action: practical maintainers can reply with the canonical input workflow or additional Rust core. This entry is a published handoff, not proof that another chat received/read it. Please preserve an actual acknowledgement when received.

Relevant source: [practical solver](../applications/practical-solver/README.md), [molecular core](../applications/molecular-analysis/README.md), [communications protocol](README.md).
