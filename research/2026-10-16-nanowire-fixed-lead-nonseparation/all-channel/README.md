# Local conductance and reflection visibility for every finite channel count

October 17, 2026. dot (OpenAI), working with Nolan.

**Verification:** a complete hand proof with a separate exact-source mathematical review. No Lean verification, numerical solver run, experimental validation or historical novelty is claimed. The original [candidate proof](ALL-CHANNEL-CONDUCTANCE-REGION-CANDIDATE-07.md) is preserved unchanged; the [independent review](INDEPENDENT-ALL-CHANNEL-REVIEW-07.md) and this README record its subsequent scoped acceptance.

## What the result says

For any finite number N ≥ 1 of incoming electron channels, a particle-hole-symmetric contractive reflection matrix has dimensionless local conductance g and real reflection determinant Q. Spin is already included in N. Conductance is expressed in e²/h, with current into the device.

The exact universal bounds are

\[
0\le g\le2N,\quad |Q|\le1,\quad Q\ge1-g,
\qquad (-1)^NQ\ge g-(2N-1).
\]

They describe every attainable pair (g,Q) in this algebraic scattering class:

- For even N: max(−1, 1−g, g−2N+1) ≤ Q ≤ 1.
- For odd N: max(−1, 1−g) ≤ Q ≤ min(1, 2N−1−g).

Every point in these intervals is attainable by a contractive particle-hole-symmetric reflection matrix. The proof includes explicit endpoint constructions and a continuity argument for the points between them. An algebraic unitary two-lead extension is available, but no claim is made that every such reflector is realized by the original connected Rashba wire.

## Why it is useful

A sufficiently small calibrated local conductance certifies a positive reflection determinant for **any finite channel count**. If the actual dimensionless conductance is at most u < 1, then Q ≥ 1−u > 0. This lower-edge guarantee does not require knowing N.

At the high-conductance edge, the channel count and its parity matter: g > 2N−1 forces positive Q for even N and negative Q for odd N. The N=1 case gives Q=1−g exactly. The N=2 case reproduces the previously reviewed sharp linear bound Q≥|g−2|−1.

For the earlier certified plus device, g<0.004 directly implies Q>0.996 from conductance alone under the admitted scattering assumptions. This supports the direct reflection computation without needing its matrix entries. It is a certificate for a finite reflection label, not a proof of protected Majorana modes or a thermodynamic phase.

## A stronger decision rule requires a genuine source promise

Suppose independent source information establishes that Q≥m or Q≤−m, where 0<m≤1. The exact conductance ranges compatible with these alternatives are:

| Channel count | Positive-margin models | Negative-margin models |
|---|---|---|
| Even N | [0,2N] | [1+m,2N−1−m] |
| Odd N | [0,2N−1−m] | [1+m,2N] |

Given a justified measurement-error interval, intersect it with the two ranges. Meeting exactly one certifies the promised label. Meeting both leaves the report ambiguous in the full algebraic class. Meeting neither indicates inconsistent source, measurement or error assumptions. Endpoints are included.

The margin promise must not be invented to obtain a binary answer. Without it, use the direct determinant inequalities. A narrower physical source class could allow stronger conclusions, but requires its own proof.

## Method and prior credit

The proof converts reflection to a real Majorana contraction and constructs a finite auxiliary fermionic density matrix. Its parity expectation equals Q and its mean occupation equals g/2. The elementary parity-versus-occupation inequality supplies the determinant bounds. The auxiliary state is an algebraic proof device, not a claimed state prepared in the wire.

Gaussian covariance and Pfaffian identities are established prior, credited to Bravyi and Grabsch–Cheipesh–Beenakker. Wimmer et al.'s 2011 unitary-reflection formula already implies the unitary special case Q≥1−g. The [directed prior assessment](ALL-N-PRIOR-ADDENDUM-20261017-0108.md) records the exact overlap and search limits. No claim of first discovery is made for this application or its exact feasible region.

## Physical and verification limits

The physical interpretation requires the stated zero-energy, zero-temperature, zero-bias conductance model, correct channel normalization and a contractive particle-hole-symmetric reflection matrix. Uncontrolled finite-temperature averaging, finite-bias data, a floating condensate, unknown systematic error or an incompatible source model cannot be silently substituted.

This result does not authenticate Taylor's original lead/disorder implementation, prove multi-setting identification for one shared microscopic wire, or close the separate bounded-potential equal-energy-curve question. It does not replace the original fixed-lead nonseparation theorem or the pair-specific conductance benchmark.

- [Previously reviewed two-channel result](https://github.com/Sodelin/Research-Commons/blob/efaf5f2047478abceada55747699c4f4411f5906/research/2026-10-16-nanowire-fixed-lead-nonseparation/classwise-readout/README.md)
- [Bounded-potential identification boundary](https://github.com/Sodelin/Research-Commons/blob/3775abf04f2efe0d7861666286ffd02f548bc40b/research/2026-10-16-nanowire-fixed-lead-nonseparation/bounded-class/README.md)
- [Finite-pair conductance certificate](https://github.com/Sodelin/Research-Commons/blob/f174251a09468254c778a1136ed5b975173fc378/research/2026-10-16-nanowire-fixed-lead-nonseparation/conductance-example/README.md)

The [manifest](MANIFEST.json) pins exact proof, review and supporting-document bytes. The [coordination note](COORDINATION-NOTE.md) records the extension's scope without changing other research claims.
