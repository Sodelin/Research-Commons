# Exact rational bank interface: retained-source implementation contract

This NEW executable component is the effective rational slice of the retained
finite-PMF pushforward construction. It does not replace its real-valued
noncomputable Lean definitions or provide physical-source admission.

## Exact source reviewed and reused

The four manifest-listed authored bodies at
fc0b9966c36e5d54eaf41edd15c8afc904200ab1,
research/2026-10-15-smt-tester-2-finite-pmf-adapter-hand-proof, were fetched and
their exact byte counts/SHA256 verified. Attribution remains the original
SMT Tester2 contributor, dot/OpenAI helper sources, CM formalization and
physical suppliers. No new grouping mathematics is claimed.

The actual sources at7239e89dea5caad68a54227cee3b44a7d9b96389 were read and
SHA256 authenticated:
- fb4b6ba74553b4ec4d93204dd38a3632227a51577aee087de4ae17758c63fe09.lean:
  positiveSupportPMF, positiveSupportPMF_positive/_sum/_map;
  finiteBankMoment p x k = sum p(a).toReal*x(a)^(k.choose2);
  configurationBankPMF and actual_randomized_legal_moment.
- ee5d196dc25a53b8d15957fcbaf9fdf13435b78eb03f8e66819d3f258f35b787.lean:
  gridWeight, gridWeight_moment, gridWeight_zero_outside and
  gridWeight_eq_mapped_mass. Its literal UNCOMPILED draft status is preserved.

The receiving CMFoundations.lean source embedded in accepted certificate
41aa9b7b3fb639d22db47fffac7f5f92bfea021bc3f3e548f6f2c3dfbb5d7d5a at
514648b697aeed8f46582109cfeefcd7707cd738 was read:
FinitePositiveLaw requires finite distinct positive real nodes, positive
on-support weights and exact mass1. Its domain is the whole positive axis.
The OLD weighted-square certificate additionally needs nodes<=1. This executable
therefore checks (0,1] only on positive-mass rows, while allowing arbitrary
well-formed rational values at exactly zero mass.

## Strict input and native output

bank_codec.py accepts exactly:
    {"schema":"rational_finite_bank_moments_v1",
     "copy_level_count":L,
     "atoms":[{"weight":"p/q","survival":"a/b"}, ...]}

L is a JSON integer1..8; the carrier has1..256 rows. Strings use the original
strict rational grammar and reduced128-bit cap. Each weight is in[0,1] and
total mass must be EXACTLY1. Positive weight requires survival in(0,1].
No IDs, thresholds, floating tolerance or normalization are introduced.
Duplicate JSON fields, unknown fields, booleans in place of integers and
malformed rationals are refused.

The transport wire is:
COMMON_BANK_MOMENTS_V1 L N weight1 value1 ... weightN valueN.

The separate common-bank-moments Rust executable uses the unchanged crate
dependencies and a byte-exact copy of the old narrow Input parser around the
established rational parser. The existing proposer/main remains unchanged.
It omits only zero weights; equal rational values form a BTreeMap fiber whose
weight is the sum of EVERY positive preimage mass. No positive atom is dropped.
It checks original and grouped mass, then computes every k=1..L from this one
law at exponent k*(k-1)/2. Native output is one canonical wire:
CHECKED_RATIONAL_BANK_MOMENTS_V1 L N positive_count distinct_count
  value1 weight1 ... valueD weightD moment1 ... momentL
(all tokens on one line followed by one newline).

Reduced internal arithmetic has an8192-bit ceiling; output rationals retain the
old128-bit/80-character cap. Exhaustion returns UNKNOWN with exit2. Invalid
syntax/domain or a completed mass calculation unequal to1 is REFUSED with exit1.
A bound-exhausted calculation cannot be interpreted as mass inequality or NO.

## Independent result binding and old solver composition

The Python decoder independently evaluates moments on the ORIGINAL positive
rows using Fraction arithmetic rather than relying on native grouped moments.
It verifies the complete canonical native output, exact grouped weights,
normalization, copy/exponent sequence and request identity. Its verified JSON
labels the values as DERIVED FROM THIS SUPPLIED RATIONAL LAW.

When D<=3 and L=2D+1, the report additionally supplies an exact
rational_support_acquisition_v1 candidate_request. Other bank shapes still
produce valid bank moments; requesting an unsupported acquisition shape yields
UNKNOWN. The existing support codec/proposer/checker/emitter/runtime/MCP schemas
are untouched. Both fixtures should reproduce the already published two/three
old-schema certificate IDs and exact standalone proof hashes.

To apply derived moments to externally supplied observations, equality with
each actual observation is an ADDITIONAL obligation. This adapter alone does
not identify a supplied mathematical bank with a physical source or infer
measurement provenance.

## Required Lean-side relation

For input rows (w_i,x_i), positive carrier A={i | w_i>0}, exact image S=x(A)
and W(s)=sum over i in A with x_i=s of w_i, the implementation targets:

1. S finite, distinct, nonempty; every s in S satisfies0<s<=1.
2. Every W(s)>0 on S and sum over S of W(s)=1.
3. For EVERY natural n, sum over S W(s)*s^n = sum over raw rows w_i*x_i^n.
4. Consequently each emitted moment[k-1] equals both sides at n=k.choose2,
   for all1<=k<=L, using ONE fixed row law.
5. Rational-to-real casts preserve these exact equalities, then the existing
   generated finite_supported_bank theorem can be instantiated on S.

Items1–4 are finite exact algebra explained by the retained proof/helpers;
formal compilation and the concrete cast/receiver packaging remain with the
existing Lean owner. This native prototype and differential verification do
not constitute a Lean code-refinement theorem. Zero-mass arbitrary values are
excluded from S; they are not passed as nodes to the old full-carrier hv premise.

Physical PMF toReal/cast equality, directedSurvival parameters, actual legal
readout, one common physical tuple and a fixed pushforward law across copy
levels remain separate supplier obligations. A common bank name or same p
with different x does not justify pooling laws. No whole-tree law, joint
genealogy coupling, CM-L02 physical instantiation, source YES, global NO,
all-input G3 or INDEPENDENT G4 closure follows.

Actual ONLINE result: run39675913869 at a45e8380858dbd8502d605b01bd35113957383dc PASSED. Six bank unit groups,194 banks and194 reversal controls,17 native refusals,one output-cap UNKNOWN,eight codec negatives,eight actual CLI calls and two full bank->proposer->original-runtime fixture chains passed. Ten guard receipt/stream pairs and the artifact archive were authenticated. Both emitted proof hashes equal the already published original inputs. Common-bank-moments binary SHA256 0b4efaaf6914bb7aca79bc045ccce379fd06a4d228028a6a131d941dd1bffbec; unchanged proposer SHA25640ea56c88376c27ab01141887098743188d27fceaec002052ee9404f3fca71d9. This is exact effective-rational component evidence, not formal cast/refinement or physical-source closure. The existing Lean owner retains full package assembly and its isolated job.

## General finite-PMF semantic receiver

The existing Lean owner checked CMFinitePMF.lean SHA256
f23c4428e1f5bad8f2d3675caa1684b66377acf4cfe34451b6be767d4e97d4c7
at peer311290fc03de071d634fe5c2ade857acf50d9259. Its seven complete selected
types/standard-axiom dispositions and exact source projection were independently
reviewed. This is attributed hosted Lean4.35/mathlib56a005 execution.

fromFinitePMF packages ONE supplied finite PMF and value function into the
existing CM law using original positiveSupportPMF/gridWeight, not another
grouping engine. Every natural moment equals the original weighted rows.
Only nonzero-mass rows need positive values, and the separate Ioc theorem asks
<=1 only there; zero-mass out-of-domain rows remain harmless. Its weights equal
the PMF pushforward mass at EVERY real value. This matches the native positive
image semantics without asserting a parser or BTreeMap refinement theorem.

This noncomputable receiver does not acquire arbitrary-real moments, construct
a physical provider or authenticate measured data. The534-module physical/CM
context is a prepared graph with an import-only namespace reconciliation, not
a compiled physical endpoint. Exact review scope is in
evidence/LEAN-PMF-PRELAKE-REVIEW.json.
