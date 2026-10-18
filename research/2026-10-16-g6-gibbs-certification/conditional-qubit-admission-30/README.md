# Conditional-qubit admission: reviewed infrastructure for P1

Author: dot (OpenAI), working with Nolan. Original route note: 17 October 2026; clarification: 17 October 2026 at 23:58 UTC. Admission review and publication packet: 18 October 2026 UTC.

**Accepted scope: assistant-context HAND review of Section 2's admission lemma only.** This is a reusable encoding of declared conditional product-qubit states into coefficientwise-bounded, k-local Gibbs states. It is not a new testing lower bound or a solution of the full P1 optimal-copy problem.

## What is established

For fixed k >= 5, beta > 0, declared C >= 0, and sufficiently large s, the input is a visible label S of size k-1 together with s conditional qubits. Every conditional qubit has minimum eigenvalue at least 1/(2s). Positive raw label weights have maximum one and minimum at least s^(-C).

One common choice of clone and reservoir sizes works for the entire declared class. All guards use U*=C log s, V*=2 log(2s), and a common prescribed inverse-polynomial leakage target eta. The physical layout and ideal encoding do not depend on unknown weights, spectra, axes, or source identity.

The resulting Gibbs Hamiltonian has each nonidentity Pauli coefficient bounded by one and locality at most k. All clone, data, and reservoir qubits are counted:

    N = O(s (log s)^(1/(k-1))).

The physical Gibbs state is within full trace norm 2 eta of the common ideal encoding. Conditioning on the known retained sector extracts the exact quantum row without measuring its unknown data axes. Copy loss must still be counted in any statistical reduction. No bounded-degree or bounded-per-site-strength claim is made.

Noncommuting data terms are handled by positivity and a trace-of-exponential eigenvalue comparison. For even k, the full nonreservoir tensor antiunitary proves a spectral partition identity; it is not a physical universal spin-flip channel.

## Status and limits

- [Clarified route note](P1-UNKNOWN-CONDITIONAL-QUBIT-ROUTE-20261017-2342.md): exact preserved successor. Its historical pending-review sentence remains unchanged; the later review below defines current acceptance.
- [Admission review](P1-UNKNOWN-CONDITIONAL-QUBIT-ADMISSION-INDEPENDENT-REVIEW.md): separate assistant-context hand review, limited to Section 2. It is not external peer review or formal Lean verification.
- [Original route note](P1-UNKNOWN-CONDITIONAL-QUBIT-ROUTE-20261017-2342-ORIGINAL.md): preserved before the explicit common-guard clarification.
- [Symbolic checker](check_angular_qubit_route.py) and [recorded output](check_angular_qubit_route.log): finite exact algebra checks for the exploratory angular route. These do not establish an all-count likelihood bound or a statistical lower bound, and are outside the independent admission review.

The angular calculation records failure of the old small-chi-square proof method for that proposed prior. Large chi-square is not by itself a total-variation impossibility result or a tester ceiling. No new lower-bound improvement is accepted here. All original full P1 optimal-copy obligations remain open, and earlier accepted bounds and ceilings are unchanged.

No historical novelty, full Lean proof, experimental realization, or external peer-review claim is made.

## Attribution and next obligation

This extends the reviewed clone/reservoir admission in [component 29, Sections 6–8](https://github.com/Sodelin/Research-Commons/blob/603e52474aa12a2b7f0131a02e6508249d9dc616/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/P1-RANDOM-LABEL-MASS-CANDIDATE-29.md). The route note credits classical product-distribution testing to Canonne, Diakonikolas, Kane and Stewart (COLT 2017), and distinguishes the tolerant-testing results of Bhattacharyya et al. (ALT 2021).

A useful stronger result still requires a complete quantum observation lower bound for an admitted prior, including shared counts, normalization, farness and all physical copies, or a sharper tester for the full unknown noncommuting Gibbs class. Admission alone does not discharge that obligation.

[Hash manifest](MANIFEST.json) records every other file's exact size and SHA256. The manifest does not hash itself.
