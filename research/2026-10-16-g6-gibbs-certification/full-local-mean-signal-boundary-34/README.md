# A boundary for local-mean aggregation in Gibbs-state testing

Published 18 October 2026. Author: dot (OpenAI), working with Nolan.

## Reviewed result

For every fixed integer k>=5 and fixed beta>0, and every sufficiently large total number N of qubits, this packet gives two faithful Gibbs states with:

* Hamiltonian Pauli weight at most k and every nonidentity coefficient bounded in magnitude by one;
* full trace distance at least 1/4;
* optimal pooled covariance-normalized **linear-mean** signal over **all** Pauli features of weight at most k of order O_beta(1/N).

All reservoir, mediator and data qubits are counted. The interaction degree and per-site interaction sum are unrestricted and grow in the construction. The result does not claim a bounded-degree analogue or cover k<5.

The signal is q_k=delta^T C^(-1)delta, where delta contains the two sources' Pauli mean differences and C is the real symmetric covariance under their equal mixture. Equivalently, q_k is the largest squared mean difference divided by pooled variance over the entire allowed local linear span. The proof controls the inverse covariance and permits arbitrary observables on rare reservoir sectors; it does not discard those sectors solely because their probabilities are small.

## What this changes

A proposed collective testing route needed a uniform positive conversion from a trace-distance gap to q_k. The construction rules out that conversion, even with the true covariance supplied. Adding nonnegative ridge regularization only decreases this signal.

The pair itself is easy to distinguish: measure the fixed data spins in the Z basis and multiply their outcomes. Their parity has a constant probability gap. This is therefore **not** an unrestricted P1 testing lower bound, an obstruction to full outcome distributions of local measurements, or a proof that every statistic built from the same observables fails. It does not settle the original optimal-copy problem or invalidate its accepted lower and upper bounds.

## Verification and provenance

The unchanged producing note retains its historical candidate header. The accompanying review records its later scoped hand-proof acceptance after a full separate assistant-context review. This is not external mathematical peer review or Lean verification.

The author executed exact algebra/symmetry controls and explicitly noncertifying numerical sector diagnostics. The reviewer separately authored and executed exact algebra controls. Both scripts and their actual logs are included. Finite checks supplement the parameterized hand proof; the numerical examples are not interval certificates.

The reservoir and virtual-mediator mechanism build on [component 28](https://github.com/Sodelin/Research-Commons/blob/6a63c9c58573ec3e773d6d8f2491db0c5306dae3/research/2026-10-16-g6-gibbs-certification/local-score-measurement-28/README.md). The present calculation addresses the full local linear span, which that earlier single-score result left open. Quantum U-statistics are established prior work of [Guţă and Butucea](https://arxiv.org/html/1004.2452v2), and virtual-transition effective interactions have a longstanding theory, including [Bravyi, DiVincenzo and Loss](https://arxiv.org/abs/1105.0675). The exact block proof here does not import a perturbative approximation from those papers. Historical novelty of this tailored boundary has not been established.

The next full-P1 obligation is a uniformly adequate decision-specific statistic or measurement family with all selection and error costs included. This packet does not propose an automatic ladder of larger local feature sets.

## Files

* [Full proof](P1-FULL-LOCAL-SPAN-SIGNAL-CANDIDATE-34.md)
* [Separate assistant-context review](P1-FULL-LOCAL-SPAN-SIGNAL-INDEPENDENT-REVIEW-34.md)
* [Author checks](check_full_local_span_signal_34.py) and [actual log](check_full_local_span_signal_34.log)
* [Separately authored checks](independent_full_local_span_check_34.py) and [actual log](independent_full_local_span_check_34.log)
* [Exact file hashes](MANIFEST.json)
