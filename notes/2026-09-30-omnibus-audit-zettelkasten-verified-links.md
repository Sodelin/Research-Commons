# Zettelkasten with explicit claims and evidence-bearing links

- ID / UTC date / contributor-session: zettelkasten-verified-links / 2026-09-30 / omnibus-audit
- Contributor/publisher: Codex audit chat, at Nolan's request
- Label: sourced findings plus design hypothesis; no implementation superiority or Lean build claimed
- Related: [workspace omnibus](2026-09-30-omnibus-audit-workspace-design.md)
- Observed notebook repository: https://github.com/Sodelin/ChatGPT-Zettelkastten . Repository metadata was retrieved; the contents endpoint reported that it is empty. No notebook files were written by this audit.

## Strongest defensible formulation

A readable notebook can contain an explicit graph of claims, with each substantive relation carrying the appropriate evidence or verification witness. A note is a container for one or more clearly identified claims, questions or interpretations. A formal edge connects particular claims and definitions, not an entire informal paragraph whose meaning has not been specified.

This is a proposed architecture, not a demonstrated strongest possible format. A useful notebook must preserve discovery as well as verification. Requiring every exploratory link to have a theorem would suppress uncertain but valuable hypotheses and impose unnecessary cost.

## Distinct link meanings and checks

| Relation | What can be checked | What remains outside that check |
|---|---|---|
| Navigation / discussed in | Target exists and points to the intended record/version | Topic relevance and truth |
| Source supports claim | Inspect the precise passage, methods and limitations; record attribution and scope | A quotation or source link does not mechanically prove the empirical claim |
| Analogy / proposed transfer | Explicit mapping, shared features, differences, counterexamples and task tests | Similarity does not imply equivalence or a valid transfer theorem |
| Computational relation | Reproducible code, inputs, environment and tests; optionally a finite exhaustive check | Ordinary tests do not prove all inputs or the validity of the real-world model |
| Mathematical implication / equivalence | Lean theorem with named assumptions and definitions, proof build and dependency audit | Whether those definitions and assumptions correctly describe the target phenomenon |
| Supersedes / contradicts | Versions, dates and the exact competing claims; a formal contradiction only where the claims are formal | The newest record is not automatically the most accurate one |

All levels are useful. They describe the nature of the evidence, not a universal ranking in which formal proof replaces observation.

## Minimal edge record

Start with plain Markdown. When a link asserts something consequential, record:
- source claim ID and target claim ID;
- relation type and one precise assertion;
- scope and required assumptions;
- source passage, experiment, code artifact or theorem identifier;
- status: proposed, reviewed, tested or formally checked, as applicable;
- relevant definition/claim versions and actual validation record.

Capture rough ideas with less metadata; enrich links when they are reused or become important. Record proof toolchain/library versions and commit identifiers for formal artifacts. Do not tag generated Lean text as checked until it has actually built and its assumptions have been inspected.

## What a formal link means

An implication link should express a specific statement such as: under assumptions H, proposition A entails proposition B. If another edge takes B to C, composition is justified only when the intermediate propositions, definitions and assumptions are compatible. The resulting inference retains the required assumptions of both steps.

An analogy link cannot be composed that way. A related-to B and B related-to C does not establish that A entails C. An empirical association is not a causal implication. An equivalent-looking formula in two fields needs a specified interpretation before a theorem transfers.

Lean checks formal reasoning relative to its logic and declarations. Its official documentation explains that axioms are postulated and that dependency tracking permits auditing them; inappropriate extra axioms can undermine a proof. Therefore declaring a desired conclusion as an axiom does not verify a notebook connection. Proof checking does not establish the empirical truth of modeled assumptions.

## Useful prototype, avoiding decorative formalization

Choose one existing consequential mathematical result and its intended reuse, rather than spending on a new proof of elementary logic. Store a human-readable explanation and pointer to the existing theorem. Create paired transfer cases:
1. a valid reuse with the necessary assumptions and matching definitions;
2. an invalid reuse missing an assumption;
3. an attractive analogy that must remain tentative;
4. a changed formal dependency or claim binding requiring revalidation.

First check record integrity and evidence status. Where an existing Lean project is available, check the mathematical application there. Then ask a fresh researcher to use the records without treating exploratory links as proven inferences. Compare against the same source material without the additional edge records, measuring errors and capture/review/retrieval effort.

There are two distinct hypotheses: certificates reduce unjustified inference; explicit records improve task performance at acceptable maintenance cost. A passing Lean build can address the first only for the encoded formal statements. The second requires workflow evidence. No such prototype test was performed in this contribution.

## Prior research and limits

A-MEM demonstrates a Zettelkasten-inspired memory system with structured notes, dynamic indexing/linking and memory evolution. Its reported memory results motivate studying organization; they do not certify generated semantic links as mathematical theorems.
- https://arxiv.org/abs/2502.12110
- Official system: https://github.com/agiresearch/A-mem

Lean reference: propositions, axioms and proof dependencies.
- https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/
- https://lean-lang.org/doc/reference/latest/Axioms/

Repository renaming is supported for repository administrators. GitHub redirects ordinary repository access after renaming, but GitHub Pages URLs and references to hosted Actions need separate handling; avoid reusing the former name because that breaks redirects.
- https://docs.github.com/en/repositories/creating-and-managing-repositories/renaming-a-repository

## Implementation coordination

Keep the existing Commons/implementation chat's ownership. The new notebook can remain named Zettelkasten; the verification mechanism is an extension, not a reason to rename it. Use public ordinary Markdown notes and optional proof/code/source attachments. Preserve project proofs in their canonical project repository and link them.

Next action: the implementing chat should select one real mathematical reuse and one invalid transfer case, then implement the smallest edge record that distinguishes them. Do not install a large formalization framework before that question is answerable.
