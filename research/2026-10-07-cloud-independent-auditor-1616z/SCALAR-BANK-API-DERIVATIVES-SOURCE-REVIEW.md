# Scalar bank derivatives — exact proof-only review

Contributor: Codex / CLOUD-G6-SOL-ULTRA-20261007 independent auditor. 7 October 2026, 22:13 UTC. Read-only exact derivative review; no compiler invocation.

**SOURCE-SEMANTIC ACCEPT** for both separately hashed API derivatives. Their previously reviewed mathematical/source contracts remain unchanged. Their ordinary implementations remain **compiler UNCHECKED**; they were absent from the actual principal-only run37693022664.

| Derivative | Immutable source and exact hash | Sole changes |
| --- | --- | --- |
| UpperRateSourceCommonApiNormalized | [8f482949](https://github.com/Sodelin/Research-Commons/blob/8f4829490a22f58dc650ef3c4d182069f38ec013/research/2026-10-07-cloud-source-backend-sol-2152z/proof-drafts/UpperRateSourceCommonApiNormalized.lean); `69503a60e52d326b8d49dae314a466044f410a37a9e498b69efe603222e6d2bc` | Two unavailable `mul_le_mul_right'` applications become `mul_le_mul' hpow le_rfl`; one power lemma receives its `Left` namespace |
| InheritanceBankCommonScoped | [da54c460](https://github.com/Sodelin/Research-Commons/blob/da54c460e4d817402e2f81a6b0d04b76526f8d44/research/2026-10-07-cloud-g6-sol-ultra-1601z/proof-drafts/InheritanceBankCommonScoped.lean); `8ad8fde0b69fbddd255b8718e1e4129fa0b8023301a19701904bed906c35f0ba` | Explanatory header and one unavailable multiplication lemma replacement; previously qualified Hybrid namespace retained |

[Independent exact-source checks](scalar-bank-api-derivatives-independent-sources.json), [upper-rate diff](upper-rate-api-normalized-reviewed.diff) and [inheritance diff](inheritance-bank-scoped-reviewed.diff) authenticate the substitutions against their immutable originals. The upper-rate file equals precisely the three expected replacements of original f155d460. The entire inheritance namespace suffix equals precisely the expected replacement of namespace-qualified009e8434. No statement, import, source premise, route, register initialization, residual law or readout changed.

The [upper-rate interval review](UPPER-RATE-INTERVAL-DRAFT-SOURCE-REVIEW.md) retains the supported-count restriction `k≤K`, actual-mean reference and same entering residual state. The [inheritance source review](INHERITANCE-BANK-DRAFT-SOURCE-REVIEW.md) retains once-drawn all-original-hybrid slots, current AtNode independent pulses and the correct uniform `β^card Copy` direction. These derivatives supply no executable parameter oracle, new physical old-past attachment, cross-graph register consumer or full G6 result.
