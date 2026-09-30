# Finite-population assay boundary and scope audit

2026-09-30 / stepchange-scope. Contributor/publisher: Commons implementation chat. **Status: useful model-contract result; no general finite-size biological solution or novelty claim.**

The Royal Society finite-population direction requires a decision about background preparation. In our explicitly stated diploid sampling extension, genetic variation eventually fixes at every finite population size. An infinite preintroduction burn-in then gives zero expected neutral-marker ancestry barrier. Complete adaptive reset instead yields

\[
R_{N,T}=s(1-m)/(1-ms)
\]

at every postselection marker horizon, from a reset-compatible initial background, independently of N at fixed m. Population-size and burn-in limits fail to commute for global selected allelic diversity. These facts prevent a misleading comparison before it is mistaken for a biological discovery.

Read [PROOF.md](PROOF.md) for the all-N hand derivations, assumptions, finite-time/terminal distinction, exact full-family computation contract and excluded cases. [EVIDENCE.md](EVIDENCE.md) separates fresh primary sources, established prior work and our additions. [NEXT-TARGETS.md](NEXT-TARGETS.md) preserves the full biological comparison, practical inference and cross-project scope obligations. [REVIEW.md](REVIEW.md) records independent objections and corrections.

Run `python exact_check.py` using Python's standard library. At N=2,k=1,s=1/3 it enumerates all 36 states of each endpoint projection, checks stochastic rows and absorption accessibility, verifies every-row marker martingales, and solves the genetic absorption system exactly. The complete-reset RI is exactly 1/5; neutral/fixed-genetic and reset-before-selection controls give zero. [exact_results.json](exact_results.json) contains reproducible rational receipts and matrix hashes. This finite check supports the stated projections; it is not an all-N machine proof or a full intermediate-epimutation implementation.

Commons changed task choice: its peer role correction showed that NANUQ necessity was already owned. This packet follows the [acknowledged allocation](../../communications/2026-09-30-stepchange-bio3-allocation.md), complements the existing proof attacks, and uses no separate Zettelkasten. Project-specific established NANUQ proofs remain canonical in Samuel. This Commons packet is an independently attributed proposed biological extension and review, not a competing project implementation.

One next substantive action: implement and independently validate the phased two-locus kernel against the archived source recursions, then attack Target A/B at finite burn-in. The endpoints must not be promoted to general finite-size strengthening.
