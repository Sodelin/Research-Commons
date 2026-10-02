---
title: "Bounded proof-producing SMT pilot: cvc5, CPC, Logos and Ethos"
author: "GPT-6.1 Sol, distinct proof-producing SMT methods-audit lane"
coordinator: "dot"
date: "2026-10-02"
status: "Completed synthetic checked-certificate pilot; Logos build UNKNOWN; no new G closure or imported Lean theorem; prepared for authorized research publication"
---

# Result

**An actual end-to-end certificate route works here:** pinned cvc5 emits CPC refutations, a separate pinned Ethos checker accepts them, and the final input-binding/checking pipeline rejects changed assumptions, corrupted inference steps and explicit trust steps. The two positive fixtures are Boolean and quantifier-free rational-coefficient linear arithmetic. A successful run takes about a quarter second after installation.

**The proposed cvc5→CPC→Logos route did not reach checker execution within the bounded build.** Its generated checker module exceeded the 60-second pilot limit. That outcome is UNKNOWN, not an accepted Logos proof. We stopped it and tested the materially independent C++ Ethos checker instead. Ethos shares the CPC rule specification with cvc5, but has a different implementation, parser and runtime from Logos.

The achieved endpoint is **a checked CPC certificate with a trusted checker/signature/parser and an unverified input-binding adapter**. It is not a locally recompiled Logos soundness theorem, an imported Lean proof of the encoded query, or a Lean theorem of an intended original G statement. No G3, G4, G7 or full-program closure is claimed.

# Scope, provenance and compatibility

Work ran on the dot cloud Linux x86_64 host, with GPT-6.1 Sol, using public/synthetic mathematical inputs. Only official upstream source/release artifacts were downloaded. Existing Lean/source files were untouched; the Lean owner confirmed no legacy heavy build was active before the bounded checker build.

| Component | Exact tested provenance | Outcome |
|---|---|---|
| cvc5 | official release1.4.1, git2b2e844; Linux x86_64 non-GPL static release artifact; published2026-09-25 | solver/proof generation operational |
| Solver configuration | binary reports unrestricted build and `safe-mode:no` at compile time; invocation explicitly uses `--safe-mode=safe --dump-proofs` | runtime safe restrictions accepted; not a claim that this binary was compiled with `configure.sh safe` |
| Logos candidate | release-pinned `49f4fd1f256f5504f1a21c61c1808ffc56eeb6b8` | build bounded-timeout before checker exists |
| Logos toolchain | upstream file pins Lean4.33.0; tested installed Lean4.33.1, commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6 | two small modules compile; full compatibility unestablished because the generated module timed out |
| Ethos fallback | release-pinned `08e4aa40c4f8a6e00833f10e8d8985777e424027`; executable reports0.2.5 | actual certificates checked |
| CPC signature | `proofs/eo/cpc` from the same cvc5-1.4.1 source archive | no expert signature loaded; no trust rule used in positive proofs |
| Build dependencies | g++14.2.0, installed GMP headers/library, Python3.12.14 | existing; no system-wide installation |

Release and main pins differ: main's downloaded helper names Logos `d15506ec35b7a8e7aef76b4765700b7b968b2865`. We paired the solver release with its own pin rather than mixing snapshots. The release helpers are preserved. [Release Logos helper](https://github.com/cvc5/cvc5/blob/cvc5-1.4.1/contrib/get-logos-checker), [release Ethos helper](https://github.com/cvc5/cvc5/blob/cvc5-1.4.1/contrib/get-ethos-checker)

The cvc5 release ZIP SHA256 is `2f8efe58fe27ba7bccbb504533f690b9312d69da14192712460e4a19231f02a1`, matching the digest in the official release API. Source archives, binaries, inputs, proofs and scripts have separate recorded SHA256s. The public reproduction script fetches only four pinned artifacts and verifies their saved digests. Downloaded source trees/binaries are excluded from the proposed publication packet.

# Exact obligations and actual proofs

`inputs/lra.smt2` declares x,y of sort Real in QF_LRA and asserts:

- x ≥ 1/3
- y ≥ 2/3
- x+y < 1

This is the negation of the elementary lower-bound implication. It resembles a small linear side condition in probability/moment work, but is explicitly synthetic. It uses exact SMT-LIB division constants, not floating-point numbers.

`inputs/bool.smt2` uses QF_UF with only Boolean constants a,b, and asserts a∨b, ¬a, ¬b. There are no uninterpreted functions or sorts despite the broad logic label.

The exact successful solver command is:

    cvc5 --safe-mode=safe --dump-proofs inputs/lra.smt2

The solver outputs `unsat` followed by an actual CPC proof: **33 inference steps, three assumptions, thirteen rule kinds** for LRA; **three steps, three assumptions, three rule kinds** for Boolean. Complete stdout and the extracted unmodified proof bodies are retained. The framing extractor requires `unsat`, the outer opening/closing parentheses, and preserves the complete inner proof.

An earlier command also set `--proof-format-mode=cpc --proof-granularity=dsl-rewrite`. Safe mode rejected the expert proof-format option even though CPC was already its current value. Its exit1/stderr is retained. The successful command uses the permitted safe defaults; it does not claim the rejected granularity setting was applied.

# The binding check was necessary, and uncovered a real invocation hazard

Plain Ethos correctly validates a refutation of the assumptions written in the proof. That alone does not establish that those assumptions belong to the intended input.

Our first invocation used `--reference=original.smt2` together with a separate proof filename. On this pinned version, it reported `correct` even when the reference was changed to the satisfiable obligation y≥1/3 instead of y≥2/3. The same altered input is `sat` in cvc5; x=y=1/3 is a direct rational witness.

Source inspection explains this invocation behavior: `State::includeFile` unconditionally assigns `d_hasReference=isReference`; loading the main proof file after the CLI reference clears the flag. An explicit reference command inside the proof keeps it active, but leaving proof declarations in place shadows the reference declarations and rejects even the original fixture. All these outcomes are retained; **the initial files named `*-check-bound` in `pilot-runs.json` do not constitute successful binding evidence**.

The final adapter performs two checks:

1. Independently parse the restricted input/proof syntax, require identical Real/Bool declarations and the exact assertion multiset after proof-alias expansion and exact constant-rational normalization. Reject other input commands, multiple/non-final queries, unsupported operators, nonlinear variable multiplication, nonconstant/zero division, cyclic aliases and explicit trust steps
2. Only after declaration equality is checked, remove the redundant proof declarations and write a wrapper containing the CPC include, an explicit reference to the original query, and the proof body. Ethos then checks the original-input membership and the refutation within this correctly scoped wrapper

The adapter/parser is small and inspectable, **not formally verified**. It is a pilot gate, not a production SMT-LIB frontend. No semantic normalization beyond the declared exact constant arithmetic and alias expansion is silently allowed. The native reference checker additionally accepts the original wrapper and rejects the changed-reference wrapper at assumption@p2. [Ethos reference semantics and limits](https://github.com/cvc5/ethos/blob/08e4aa40c4f8a6e00833f10e8d8985777e424027/user_manual.md#validation-proofs-via-reference-inputs), [observed include-state assignment](https://github.com/cvc5/ethos/blob/08e4aa40c4f8a6e00833f10e8d8985777e424027/src/state.cpp#L325-L327)

# Measured receipts and negative controls

The core solver/checker runs have a20-second timeout and2GiB virtual-address cap in the bounded runner; the final adapter also applies that cap to its checker. Builds use60-second bounds. Raw stdout, stderr, exit statuses and exact commands are saved; no UNKNOWN/error is converted into a theorem.

| Run | Result | Measured wall time |
|---|---|---:|
| Generate LRA CPC | UNSAT plus33-step certificate, exit0 | 0.01426s |
| Generate Boolean CPC | UNSAT plus3-step certificate, exit0 | 0.01294s |
| Final LRA binding + scoped Ethos | CHECKED_CERTIFICATE, exit0/correct | 0.27276s including Python startup |
| Final Boolean binding + scoped Ethos | CHECKED_CERTIFICATE, exit0/correct | 0.26473s including Python startup |
| Alter original y bound to1/3; keep old proof | BINDING_REJECTED; mismatch, exit1 | 0.03545s |
| Change final eq_resolve premise@p20 to@p4 | binding passes; Ethos rejects the inference, SIGABRT/exit−6; adapter exit1 | 0.27980s |
| Replace derivation with trust(false) | adapter rejects trust, exit1 | 0.03341s |
| Raw Ethos on trust(false) | **incomplete with exit0** | retained receipt |
| Logos sequential import pilot | UNKNOWN:60.08s bounded timeout; no Cpc.Logos object | 60.08185s |
| Independent Ethos build | executable present, exit0 | 14.79282s |

The solver/checker orchestration's cumulative child max RSS was22,840KiB; the compiler-build process cumulative child max RSS was252,624KiB. The Logos pilot cumulative child max RSS was1,177,352KiB. These are process/accounting observations, not sums across subprocesses, per-tactic allocations or production benchmarks. Final Python-wrapper RSS figures in receipts are not substituted for total descendant memory. Bounded computations either completed or were stopped at their limits, with small timer/teardown overhead; no larger-build escalation was used.

The Logos attempt compiled Cpc.SmtEval in0.514s and Cpc.LogosTerm in4.607s, then timed out on the938,865-byte generated Cpc.Logos source after54.961s. It used Lean-j1/-M2048 and a separate object directory. No API/soundness theorem or checker executable was built. Upstream describes an approximately3.5-minute first executable build and a much larger full proof development; neither was undertaken. [Pinned Logos build/correctness documentation](https://github.com/cvc5/logos/blob/49f4fd1f256f5504f1a21c61c1808ffc56eeb6b8/README.md)

CMake was not installed. Inspection showed `src/CMakeLists.txt` simply globbed the checker C++ sources and linked GMP. A direct equivalent C++17 build of those22 files, without optimization, plugins or source edits, completed. Its exact command is in `ethos-build.json`; this is not a claim that a CMake test suite passed.

# Trust and semantic translation

The final assurance path is:

    intended source mathematics
      → human-reviewed encoding (still required for any G application)
      → exact one-query Boolean/QF_LRA SMT-LIB fixture
      → cvc5, treated as an untrusted certificate producer
      → actual saved CPC refutation
      → unverified strict declaration/assumption-binding adapter
      → explicit scoped reference + Ethos parser/checker + GMP + pinned CPC rules
      → checked certificate of the encoded obligation

There is **no arrow here to a new Lean kernel theorem of the original source statement**.

Ethos checks the derivation against the supplied Eunoia calculus; its C++ implementation and parser are trusted, and it does not prove that the calculus itself is sound. Acceptance therefore requires exact `correct`, a zero exit and a final top-level false via `--require-proof-of-false`, not merely an exit-zero process. The explicit trust control demonstrates why this matters. [Pinned Ethos README](https://github.com/cvc5/ethos/blob/08e4aa40c4f8a6e00833f10e8d8985777e424027/README.md)

All sixteen rule kinds actually used have corresponding source proof files at the release Logos pin. Inspection found no standalone sorry/admit/axiom tokens in those files; the upstream textual hygiene script passed over887 Lean files. None of those soundness proof modules was kernel-compiled in this pilot. Textual hygiene and a version pin are not a substitute for that compilation. The exclusion definitions inspected concern lambda/beta-reduce, unused here; expert rules and trust steps are likewise unused. `rule-trust-inspection.json` records source filenames/hashes and explicitly marks local kernel compilation false.

Logos's model interprets Real as ℚ, arrays as almost-constant maps and uninterpreted sorts as infinite. Its documentation states that these narrowings do not change the quantifier-free linear fragments; nonlinear real uses may change the meaning without producing an incomplete warning. Our fixtures use no arrays, sorts, quantifiers, nonlinear variable products, transcendental functions or division by a variable. In the LRA fixture, adding two lower bounds and the exact identity1/3+2/3=1 works over both rationals and reals. More generally, rational-coefficient linear feasibility has a rational witness whenever it has a real witness; this equivalence does not extend to a constraint such as x²=2. [Pinned semantic conformance](https://github.com/cvc5/logos/blob/49f4fd1f256f5504f1a21c61c1808ffc56eeb6b8/docs/smt-lib-conformance.md)

Logos's proof-file parser and correspondence with the original input are also outside its soundness theorem. Even a future Logos `correct` verdict needs original-input binding and an audited source→SMT translation. A Lean-written checker is not automatically a returned Lean proof. [cvc5 CPC/Logos fragment and pin discipline](https://cvc5.github.io/docs/cvc5-1.4.1/proofs/output_cpc.html)

# Fit to actual G3/G4/G7 work

- **G3:** rational-coefficient linear side inequalities after fixed constants and already-established semantic identities are good candidates. The actual finite-moment barrier contains variable products, squares and a finite-sum identity; cap-six determinant/resultant and all-factor attainment/completeness are not this safe linear fragment. Replacing those by free variables requires separate proved implications. Existing exact algebra→Lean certificates remain the stronger endpoint
- **G4:** the subgoal x<1 and y<1 implies x+y<2, used before a fourth-power positivity argument in the balanced-forest theorem, fits QF_LRA directly. The full balanced residual and arbitrary-interior-weight defect identities are nonlinear polynomial statements and were not tested or certified by this route. Same-L arbitrary-chain stopping remains a separate unbounded endpoint
- **G7:** fixed original-source count constraints and the final integer-linear rearrangement of the graph census fit bounded Boolean/QF_LIA reasoning, provided degree sums, natural-number domains and original edge IDs are faithfully encoded. This pilot tests Boolean/LRA, **not QF_LIA**. Existing source-facing Lean census proofs already use omega; replacing them solely to add this checker is not justified. It does not certify original graph semantics, universal source enumeration, response-rank procedures or a global optimizer

This route can improve auditability of future **hard bounded encodings** by preserving proof output instead of a bare UNSAT string, and by independently rejecting solver/certificate mistakes. It does not supply the missing source translation or reduce the logical trust base below existing completed Lean proofs. No speedup on a real G query was measured.

# Actionable next step and reproducibility

Adopt the receipt/gating contract for suitable future bounded queries. For the next real case, freeze one source-adjacent linear/Boolean obligation, prove or review its encoding, run these same positive/mismatch/corruption/trust controls, and preserve the complete artifact. Require UNKNOWN propagation, version/fragment pins, explicit reference scope, and `correct` plus top-level false.

If the required endpoint is a Lean kernel theorem, choose an explicit Lean reconstruction/checker integration with proved encoding, or budget a separately authorized pinned Logos/toolchain and used-rule soundness build. The stopped60-second build is not enough evidence for that endpoint; another identical attempt is not currently useful. No broad proof-tool suite installation is recommended.

Reproduce the independent certificate endpoint from this directory:

    python3 scripts/fetch_vendor.py
    python3 scripts/build_ethos.py
    python3 scripts/run_pilot.py
    python3 scripts/test_bound.py

`run_pilot.py` intentionally preserves the preliminary CLI-reference experiment as a negative audit lesson. **`test_bound.py` is the final acceptance contract**, using `check_bound.py`, with expected exits0,0,1,1,1. Run `build_logos_interpreted.py` only to reproduce the stopped bounded attempt, using the saved module order; it is not needed for the passed Ethos route. The complete pinned helper/source links and artifact hashes are in the manifest and receipts.

## Acceptance ledger

1. Exact input, theory, flags and versions preserved: PASS
2. Solver emits actual proof/certificate: PASS
3. Compatible separate checker accepts the positive certificates: PASS, Ethos; Logos NOT REACHED
4. Corrupted proof and altered obligation rejected: PASS in the final combined pipeline; the altered obligation fails binding, and a separately scoped native reference check also rejects it
5. Unsupported/trust rules, safe fragment, checker trust and semantic translation inspected: PASS at the declared audit depth; local Logos proof-module compilation NOT PERFORMED
6. Assurance level stated accurately: CHECKED CERTIFICATE of synthetic encoded statements; no new original-source/Lean G theorem
