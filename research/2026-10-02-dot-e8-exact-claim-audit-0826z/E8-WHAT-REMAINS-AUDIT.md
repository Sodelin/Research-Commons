# E8 what remains: theorem, formalization and runtime boundary audit

Attribution: dot. 2026-10-02. Read-only audit; no new proof expansion.

## Short answer

The remaining E8 endpoint is chiefly **formal source refinement and
implementation verification**, not a list of open mathematical conjectures.
The original paper already proves its abstract RNA recurrence contract.
The actual pinned re-expression, outputs, factors, numerical arithmetic and
randomness still have to be linked to that contract. Some tempting source
premises are already known to fail and cannot be labelled merely unfinished.

## 1. Already established mathematics/paper/library results

- CParty§4 Theorem1 gives completeness, correctness and unambiguity of its
  Z_W recurrence for the stated hierarchically constrained density-2
  ensemble. Its proof is structural induction over disjoint terminal cases;
  the asymmetric VPR/VPL decomposition prevents alternative derivations
  converging on one structure. This is a paper result, not an open grammar
  conjecture. Source:
  [CParty](https://academic.oup.com/bioinformatics/article/41/1/btae748/7928840).
- PRISM§2.1 already gives the conditional contribution selection rule and
  recursive cancellation yielding the Boltzmann structure law, assuming
  the same exhaustive/disjoint recurrence contributions and uniform choices.
  Source: [PRISM paper, p30:5](https://drops.dagstuhl.de/storage/00lipics/lipics-vol390-wabi2026/LIPIcs.WABI.2026.30/LIPIcs.WABI.2026.30.pdf).
- Generic weighted-derivation evaluation and its optimization/partition/
  sampling applications are inherited from
  [Ponty–Saule](https://arxiv.org/abs/1106.3771). Generic verified memoization
  and bottom-up correspondence have
  [AFP Monad_Memo_DP](https://isa-afp.org/entries/Monad_Memo_DP.html) as direct
  mechanized prior. Neither automatically instantiates the pinned source.
- Supported probabilistic composition and finite output-fiber aggregation
  already exist in
  [mathlib PMF](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/ProbabilityMassFunction/Monad.lean)
  and [finite PMF constructions](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean).
  They are not new E8 discoveries.
- Inverse-CDF selection, finite-grid counting, kernel-error composition and
  observable pushforward are standard mathematics. E8's15 checked modules
  are local formalizations/source checks; none presently supplies a new
  mathematical theorem claim.

## 2. Missing Lean ports or instantiations of established results

| Obligation | What is known already | Exact missing formal link |
|---|---|---|
| Scaffold/tree helpers | Standard balanced-tree/Euler/LCA facts | Mechanize the selected constructor/parser model and derive the precise border/endpoint guards used by the source-shaped child theorem |
| Source generated-list binding | The C++ factory and its manual overrides are available; enums/normalizer transcribed | Prove that actual emitted ordered children satisfy the Lean transcription/family/local-guard interface, including three WMBP manual paths and W(i,i) |
| Root carrier/order | Standard finite DP theorem is checked; the tested root cones have no future edges | Derive all-input source reachability/zero-support/order invariants on the original root carrier, then instantiate the existing interpreter theorem |
| Paper RNA decomposition | CParty Theorem1 supplies the mathematical completeness/unambiguity target | A Lean port or a precise source-to-paper refinement proving the17-family re-expression represents the same structures exactly once |
| Traceback semantics | PRISM cancellation and support-aware composition are known | Bind actual continuation states, exhaustive production lists, factor/child totals and finite total-production count to those laws |
| Observable law | Pushforward/fiber-sum theorem is checked and exists in mathlib | Bind emitted pair maps and the actual selected classifier to the intended observable; this is not supplied by an arbitrary classifier argument |

These are substantial verification tasks but should not be advertised as
unsolved general mathematics. The current15th boundary theorem proves
right-bound/same-right progress **from explicit local numeric guards in a
manually source-shaped function**. It does not prove those guards for the
C++ factory, the parser-to-tree correspondence, or root-order admissibility.

## 3. Runtime-specific assumptions that remain unverified or need correction

1. **Executable admission/defined memory.** The original ExactSession checks
   nonempty sequence and equal lengths, not balanced scaffold prefixes,
   pairing/sequence policy or intrinsic helper size. A private guarded
   wrapper now narrows the accepted domain empirically, but its complete
   source/refinement/resource/failure contract is not a Lean theorem.
   The conditional RMQ helper domain n≤8193 has a source-arithmetic receipt;
   it is not full C++ memory safety or a promise of available RAM/stack.

2. **Original root-reachable engine correctness.** Full raw all-cache-cell
   precedence/recurrence fidelity is false at the pin: a balanced canonical
   source witness has positive off-root omitted contributions. The root
   remains correct on that fixture. The chosen endpoint preserves current
   execution and proves root-reachable/output correctness; a universal
   all-cache-cell assertion must not be used as its premise. Observer-frame
   read/write admission has a full57-rule source audit, subject to serial,
   frozen-input/configuration and defined-memory conditions, not a formal
   C++ alias/compiler proof.

3. **Code-to-paper factors and scaling.** The VPR empty-right factor uses
   left padding in the public PF/trace source although the original CParty
   recurrence and PRISM minimum-energy backend use right padding. That
   mismatch is verified, and isolated source-faithful corrections pass
   bounded tests. They are not an all-rule/all-parameter factor proof.
   Remaining coefficient ownership/BE/support/scale contracts must be
   established for actual reachable derivations. A generic semiring theorem
   cannot repair wrong supplied factors.

4. **Output/support/multiplicity binding.** The source exports generated
   Round and Square pairs, removes fixed-G pairs and renders the union.
   Prove every reachable output satisfies the paper's fixed-G/disjoint,
   pseudoknot-free G′ and density-2 conditions, that every paper-admissible
   output is represented, and that representation has the intended
   multiplicity. The API documentation's lane/ownership description is not
   that proof; no support counterexample was found in the bounded screen.

5. **Fixed-target evaluator completeness and mass.** SCFG2 uses MaxProduct
   for a target-filtered evaluator. Under a proven one-derivation-per-target
   contract its value is the structure weight. Without that contract it
   need not be a SumProduct mass, and an arbitrary class filter needs a sum
   over all matching outputs. The public README itself lists target-filter
   completeness and independent re-expression unambiguity as non-guarantees.

6. **IEEE arithmetic and exponential weights.** The exact-semiring
   derivation-sum theorem does not apply automatically to double operations,
   which do not satisfy exact ring laws. Establish represented-vs-physical
   factor error, exp/rounding/underflow/overflow handling, accumulation error
   and selector comparison error on the admitted parameter domain. No
   uniform exact real-law claim is justified for arbitrary numerical inputs.
   Existing certified numeric techniques may be reused; no complete
   source-specific certificate is present.

7. **Actual randomness.** The finite-grid theorem assumes fresh conditional
   uniform grid inputs, while an explicitly seeded PRNG is deterministic
   given its seed. A seed option alone does not verify independence or the
   required conditional law. Choose and prove the intended entropy/PRNG
   contract or quantify the discrepancy. Exact-bit/rational samplers such
   as [FLDR](https://proceedings.mlr.press/v108/saad20a.html) and verified
   primitives in [SampCert](https://arxiv.org/abs/2412.01671) are prior reuse
   candidates, not proofs of this C++ source's Boltzmann/PRNG behavior.

8. **Compiler/extraction/parameter environment.** Bind the formal reference
   to the actual compiled C++ source, vendored energy library, immutable
   parameter snapshot and serial execution. Compiler hashes and successful
   runs are reproducibility evidence, not a semantics-preserving compilation
   theorem. Required trust boundaries must remain explicit if not verified.

These are implementation-specific obligations, not established new
conjectures. Some may require a repair or a weaker, precisely admitted
contract rather than a proof of the old unrestricted assertion.

## 4. What is outside this endpoint

Correctness in a defined thermodynamic model does not prove that the model
is a universally accurate account of biological folding. Arbitrary-class
efficient aggregation also does not follow from semiring inside correctness;
compositional classifier/output-language restrictions and complexity need
their own applicable prior contracts. General pushforward mass identities
remain known even if a concrete efficient classifier inverse-image program
has not been implemented or verified.

## Evidence anchors

- [SCFG2 public guarantee/non-guarantee contract](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/README.md)
- [API output/serial-environment boundary](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/api/README.md)
- [Off-root premise check/root distinction](https://github.com/Sodelin/Research-Commons/blob/76cedc39ef624cb26312d22db4947d46b23b7a4b/research/2026-10-02-dot-e8-provider-premise-0754z/SCFG2-PROVIDER-PREMISE-CHECK.md)
- [Independent physical/root diagnostic](https://github.com/Sodelin/Research-Commons/blob/ccedf5da2c3b16d7b3c452d916f7b410475918b9/research/2026-10-02-dot-e8-validation-root-evidence-0804z/E8-VALIDATION-AND-ROOT-BOUNDARY-CHECKPOINT.md)

Current status:15 new Lean components PASS,69 selected standard-axiom audits,
14 components published and the15th frozen locally. No end-to-end RNA source
law, biological validation or mathematical novelty is claimed.
