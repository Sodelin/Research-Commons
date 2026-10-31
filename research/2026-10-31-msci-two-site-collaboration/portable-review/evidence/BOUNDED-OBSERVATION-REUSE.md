# Retained bounded observation bridge: relevance to the two-site manuscript

This records a related existing hand result and its scope; it is not a new proof, independent human review or Lean certificate. At guide commit `501730afc601aa196ff4c7b84e96105a63199668`, `recovery/msci/MATCHES.json` maps the following complete bodies to Research Commons commit `27b143c73a4ac272b560b2974d83ff96df738531`. Each body's byte length, SHA-256 and Git blob matched that guide metadata. I read the complete contract, overview, review and relevance note, and the theorem statement and §§7–8; I did not independently audit the full proof or rerun its controls.

| Body | Bytes | SHA-256 | Upstream source |
| --- | ---: | --- | --- |
| Contract | 4,206 | `3fcc38bfcfb1b3b891270a2959d109fdaab247b5e4234d24633b428673827cbc` | [contract](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-bounded-msci-observation-bridge-0636z/CONTRACT.md) |
| Overview | 4,099 | `95cc6a164d1c7b3ea7075f3ff311264c43be79c99233eeabe92d7c9b8aad2bba` | [README](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-bounded-msci-observation-bridge-0636z/README.md) |
| Theorem body | 14,106 | `3430171e587360460219ab78549538dcce7ef395a6a6502795842893de1f33fa` | [theorem](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-bounded-msci-observation-bridge-0636z/THEOREM.md) |
| Review | 7,724 | `31fec0f7c60958677eb6a5ed3408b87c9bb82be0c9fb705c74f5b809a7cc3c88` | [review](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-bounded-msci-observation-bridge-0636z/REVIEW.md) |
| Relevance note | 5,510 | `d0de9a946de0ffd808531c700c31833d5f76fa5bf17eab8916d1b82d08ae282f` | [relevance](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-bounded-msci-observation-bridge-0636z/RELEVANCE-AND-SPECIAL-CASES.md) |

The theorem body's original header calls it a hand-proof candidate awaiting review. The separately dated review records acceptance at the contract's hand-proof scope and names `dot (OpenAI)` as reviewer; the theorem and review do not count as independent human reviews. The review reports controls, which were not rerun here. No Lean verification is asserted by those documents.

## What the retained result says

For a finite catalogue with fixed bounds on labelled samples, epoch/boundary positions and populations, the contract specifies positive within-population pair rates, finite current-block routing, a common positive-rate root tail, contemporaneous samples and a known stationary JC clock. Population paths and routing flags are marginalized; the sampled genealogy ends at its MRCA. It excludes, among other things, within-epoch migration, within-locus recombination and an unknown clock scale.

For a shared genealogy `T`, the contract writes the length-`L` locus law as `E_T[product_i p_T(x_i)]`, where `p_T` is the conditional one-site pattern law. The retained theorem states that for one explicit finite `L(n,J,P)`, equality of these complete locus laws is equivalent to equality of the corresponding route-marginal timed-genealogy laws throughout the bounded catalogue. It does not itself make the genealogy-law map injective, identify a network or direction, or supply a minimal or practical locus length. The relevance note identifies the present six-sample, fixed directed-pulse family as a special case of that broad contract.

The theorem's §7 uses known-clock JC pair correlations `exp(-(8/3)t_ij)` to recover pair ages from a conditional pattern vector, then the sample-labelled ultrametric genealogy. This is source-level guidance for the local observation bridge (internal supporting file not included: `JC-LOCUS-BRIDGE.md`): it reinforces the shared-genealogy outer expectation, pair-age and sample-MRCA boundaries. It does not establish that the local uncompiled finite-tree/PMF candidates implement `p_T`, or that their likelihood-normalization obligation has been discharged.

## What does not transfer

The broad theorem's deliberately loose finite `L(n,J,P)` is not a two-site bound. Its equality of observation and genealogy fibres is not the separately proved nine-parameter injectivity result for the fixed family. The current manuscript's two-site identification uses its own sharper source-specific argument; it must not be attributed to the broad bound. Neither result supplies finite-data accuracy, empirical admission, an implemented estimator, a biological fit or a full Lean proof.
