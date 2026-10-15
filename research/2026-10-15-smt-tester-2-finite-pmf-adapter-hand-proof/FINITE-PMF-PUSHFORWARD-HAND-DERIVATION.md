# Finite PMF pushforward: contributor hand derivation

This is a hand-derived proof of the finite adapter contract, **not a Lean
implementation, kernel-checked theorem, new CM-T02 proof or physical-source
acceptance**. It supports the existing formal/source owner without taking over
implementation or compiler scheduling. No compiler, supplied-source import or
execution, numerical calculation, test, solver, provider/model call, new worker
or executor, or physical probe was started for this derivation. Existing
parallel source/review contributors were reused.

Reuse the existing physical supplier first. Its `positiveSupportPMF` at
3008–3018 already removes only zero masses without renormalization;
`positiveSupportPMF_positive` at3020–3022 proves positive real weights using
`p.apply_ne_top`; `positiveSupportPMF_sum` at3024–3032 preserves every real
weighted readout; and `positiveSupportPMF_map` at3034–3040 preserves each
pushforward PMF. Its `directedSurvival_positive` at77–78 and
`directedSurvival_le_one` at80–83, also packaged as `directedSurvival_bounds`
at2873–2876, provide the physical range (0,1]. These exact helper bodies were
read. They should be reused, not reimplemented. Scalar grouping also already
exists in `DotG4.ActualPositiveGridUniqueness`: `gridWeight` at93–94,
`gridWeight_moment` at96–113, `gridWeight_zero_outside` at115–121 and
`gridWeight_eq_mapped_mass` at123–135. Thus the remaining bridge is typed
`FinitePositiveLaw` packaging, its positive-weight/mass1 fields, finite-sum
presentation conversions and the triangular index identity. A new scalar
grouping algorithm or moment-regrouping lemma is not needed. The derivation
below explains the finite mathematics and maps it to these existing sources.

The receiving definitions are `Astra.CommonMoment.FinitePositiveLaw` and `moment`
in the exact `CMFoundations.lean` body embedded in Research-Commons commit
`514648b697aeed8f46582109cfeefcd7707cd738`,
`research/2026-10-15-common-moment-checked-component/CM-T02-CERTIFICATE-001.json`
(33,921 bytes, SHA256
`41aa9b7b3fb639d22db47fffac7f5f92bfea021bc3f3e548f6f2c3dfbb5d7d5a`).
The Foundations body is 2,806 bytes, SHA256
`f082c4b32e4ca0a6450d0bb009a2327c3386c38c31e0d7981fab7e2b26115945`;
lines18–26 require finite distinct positive real nodes, positive on-support
weights, mass exactly1, and define the ordinary natural-power moment.

The physical supplier is Research-Commons commit
`7239e89dea5caad68a54227cee3b44a7d9b96389`,
`research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/fb4b6ba74553b4ec4d93204dd38a3632227a51577aee087de4ae17758c63fe09.lean`
(187,616 bytes, SHA256
`fb4b6ba74553b4ec4d93204dd38a3632227a51577aee087de4ae17758c63fe09`).
Its `finiteBankMoment` definition is at2775–2777,
`configurationBankPMF` at3084–3087, and
`actual_randomized_legal_moment` at3529–3539. These source lines and the
receiving definition were read; no supplied source was imported or executed.
The existing correlation contract is
`lean/CM-T02-ADAPTER-SOURCE-CORRELATION.json` (12,969 bytes at this read,
SHA256 `6a1c8803f01e1a8450061d1b7caf61cce56dd67af022196f5bd95f437cbad33a`).
The Dot scope map at `4ec6c965b2502618404c899fcf098a3b2070e63d`,
`research/2026-10-15-common-moment-checked-component/GENERAL-SPARSE-MOMENT-AND-NETWORK-SCOPE-MAP-01.md`,
is 6,858 bytes, SHA256
`954b9bbcc1fe91aad2e46b2e5f58b9d2cbf158dbb9a7f5dbc4313776af03d146`.
These pins preserve the distinct accepted abstract, historical physical and new
contributor-hand stages. The common-moment/sparse supplier retains its existing
Gemini/dot, formalization-lane, Codex physical-prior and classical attribution.

The scalar grouping source is at the same Research-Commons commit
`7239e89dea5caad68a54227cee3b44a7d9b96389`,
`research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/ee5d196dc25a53b8d15957fcbaf9fdf13435b78eb03f8e66819d3f258f35b787.lean`
(14,129 bytes, SHA256
`ee5d196dc25a53b8d15957fcbaf9fdf13435b78eb03f8e66819d3f258f35b787`).
Its literal header says `UNCOMPILED draft`. This note establishes source
availability and reads the stated lemma bodies; it does not infer compilation
from the containing folder name or attach the accepted CM-T02 certificate to
them. The abstract certificate and any historical physical/helper acceptance
remain separate evidence scopes. No new import/context selection is made here.
The helper source author remains dot / OpenAI. This new hand exposition is an
SMT Tester2 contributor proof/contract note, using classical finite-sum algebra;
it claims no new grouping method or historical novelty and changes none of the
existing helper, CM formalization, Gemini/dot or Codex physical-prior attribution.

Let I be a finite type, p a probability mass function on I, and x : I → ℝ a
total map. The exact source interface uses `[Fintype I]` and `p : PMF I`, whose
point masses are extended nonnegative reals. The one additional range hypothesis
needed to construct the positive-axis receiving law is

\[
 p(a)\ne0\quad\Longrightarrow\quad 0<x(a) \qquad(a\in I).
\tag{H}
\]

No injectivity of x, positive lower mass bound, upper node bound, or positivity
of x at zero-mass indices is required. An explicit I-nonempty premise is also
unnecessary: existence of p with total mass1 already rules out empty I. Equality
and finite image formation over real nodes are used mathematically; this proof
does not supply an effective real-equality algorithm.
The existing positive-support/image construction is noncomputable/classical
over arbitrary real inputs. All zero tests and equal-node fibers here are exact:
one may not discard a merely small positive mass or merge rounded/nearby node
values and inherit the exact theorem. Such changes require their own numerical
error contract. The existing PMF pushforward is the natural reuse route for
fiber aggregation; this hand presentation does not prescribe a new runtime
grouping algorithm. Effective representations, zero/equality procedures and any
executable receiver remain separate obligations with their existing owners.

Concretely, the source-reuse route is to take the already defined
`q = positiveSupportPMF p` on the subtype J={a : I // p(a)≠0}, let x′(a)=x(a.val),
and use `S = image x′ univ`. With w′(a)=(q(a)).toReal, set
`W = gridWeight w′ x′`. Membership x′(a)∈S is immediate, so the existing
`gridWeight_moment S w′ x′ ... n` supplies the all-natural-exponent equality on
the positive subtype. Its n=0 instance supplies mass1 after the PMF-to-real
normalization; the remaining sum conversion is between a subtype sum over S
and the receiving Finset sum. Positivity of W on S follows from an exhibited
positive preimage term. `gridWeight_eq_mapped_mass`, followed by
`positiveSupportPMF_map`, identifies the same aggregated weight with the real
mass of the original pushforward `p.map x`. Finally `positiveSupportPMF_sum`
returns the moment sum to the original carrier. These are reuse connections for
the formal owner, not new Lean code or claims that the connections have run.

1. First justify the real weights rather than assuming normalization survives
   extended-real conversion. The PMF identity on finite I is
   \(\sum_{a\in I}p(a)=1\) in ℝ≥0∞. Nonnegativity gives \(p(a)\le1\) for
   every a, hence \(p(a)\ne\infty\). Define \(w_a=(p(a)).\mathrm{toReal}\).
   Each \(w_a\ge0\); finite additivity of toReal on these finite summands gives
   \(\sum_{a\in I}w_a=1\). For a finite extended nonnegative real,
   \(w_a>0\) iff \(p(a)\ne0\). Thus neither point-mass finiteness nor real
   normalization is an extra physical assumption here: both follow from the
   exact PMF and finite carrier. They still need explicit justification in a
   future Lean construction; toReal of infinity must not be treated as a
   positive mass.

   In the supplied source, `p.apply_ne_top` already exposes point-mass finiteness.
   `positiveSupportPMF p` realizes the positive-support subtype used below, and
   `positiveSupportPMF_positive` supplies its positive real weights. This hand
   explanation is not a proposal to write a second support-reduction helper.

2. Put \(A=\{a\in I:w_a>0\}\) and \(S=x(A)\), with S a finite **set** of
   real values. Consequently equal values occur as one node. A is nonempty
   because its nonnegative weights sum to1; S is therefore nonempty. For every
   \(y\in S\), some a∈A has x(a)=y, so (H) gives y>0. Values at indices outside
   A may be zero, negative, one or arbitrary reals; their weights are exactly0
   and they introduce no node. If (H) fails at a positive-mass index, this
   construction does not meet the positive-axis input type. Deleting that
   positive mass and renormalizing would change the law and is not this adapter.

3. Define a real weight function on all real y by

   \[
   W(y)=\sum_{\substack{a\in A\\x(a)=y}} w_a.
   \tag{1}
   \]

   For every y this is nonnegative. If y∈S, choose a∈A with x(a)=y. Its strictly
   positive summand belongs to (1), and all other summands are nonnegative;
   therefore W(y)>0. If y∉S the summation is empty and W(y)=0. This canonical
   off-support value is convenient, although the receiving type places no
   condition on weight values off S. Every positive-mass original index
   contributes its full weight exactly once, including when several such indices
   have the same x value. They are aggregated, not discarded. Zero-mass indices
   may equivalently be retained as zero summands in (1).

4. The fibers \(\{a\in A:x(a)=y\}\), indexed by y∈S, partition A. Finite
   double-sum regrouping therefore gives

   \[
   \sum_{y\in S}W(y)
     =\sum_{y\in S}\sum_{\substack{a\in A\\x(a)=y}}w_a
     =\sum_{a\in A}w_a
     =\sum_{a\in I}w_a=1.
   \tag{2}
   \]

   The penultimate equality omits only zero summands. There is no rescaling or
   conditional renormalization. The data nodes=S and weight=W, together with
   steps2–4, meet every field of `FinitePositiveLaw`; call this law μ.

5. More generally, for **every total function** f : ℝ → ℝ, the same finite
   regrouping proves

   \[
   \begin{aligned}
   \sum_{y\in S}W(y)f(y)
     &=\sum_{y\in S}\sum_{\substack{a\in A\\x(a)=y}}w_a f(y)\\
     &=\sum_{a\in A}w_a f(x(a))
      =\sum_{a\in I}w_a f(x(a)).
   \end{aligned}
   \tag{3}
   \]

   In the middle equality, replace y by x(a) inside its fiber; each a belongs
   to exactly one fiber. The last equality again adds only zero terms. All sums
   are finite, so no integrability, continuity, interchange-of-infinite-limits or
   approximation assumption is used. Taking f(y)=yⁿ for an arbitrary n∈ℕ yields

   \[
     \operatorname{moment}(\mu,n)
       =\sum_{a\in I}(p(a)).\mathrm{toReal}\,x(a)^n
       \qquad\text{for every }n\in\mathbb N.
   \tag{4}
   \]

   This includes n=0: all real zeroth powers are1, including at zero-mass
   indices with x(a)=0. Such terms still have zero coefficient. The equality
   does not require strictly positive exponent or strictly positive x outside A.
   The already supplied `positiveSupportPMF_sum`, instantiated with
   `fun a => f(x(a))`, discharges the zero-removal equality. Its `_map` companion
   also shows that support restriction changes no pushforward PMF. The new
   receiving presentation groups the finite image fibers and packages these
   preserved values in the distinct-node type. That scalar grouping and
   all-naturals power identity are already expressed by `gridWeight` and
   `gridWeight_moment`; (1)–(4) explain their use rather than propose replacement
   implementations. `gridWeight_zero_outside` supplies the zero off-image fact,
   and `gridWeight_eq_mapped_mass` supplies the exact PMF-mass correspondence.

6. Finally substitute n=\(\binom{k}{2}\) in (4), for arbitrary k∈ℕ. The exact
   physical definition then gives

   \[
     \operatorname{finiteBankMoment}(p,x,k)
       =\operatorname{moment}\!\left(\mu,\binom{k}{2}\right).
   \tag{5}
   \]

   This is not an identity with ordinary moment index k. Equation(5) is valid
   also at k=0 or1, when the exponent is0. The physical legal-observation lemma
   separately requires k>0; the adapter does not remove that requirement.
   Positive copy levels1,2,3,4,5 correspond to exponents0,1,3,6,10. For a general
   application of the already accepted sparse theorem, exponent distinctness
   and support-cardinality hypotheses must still be supplied for the chosen
   inputs; this proof does not make arbitrary exponents physically observable.
   The map k ↦ k.choose2 is not injective on all naturals: k=0 and1 both give0.
   On positive natural copy levels it is strictly increasing, since increasing
   k to k+1 adds k>0 to the exponent. Thus distinct positive choices supply
   distinct triangular exponents, while arbitrary CM exponents remain a
   different input contract.

Each single moment vector used in CM-T02 must belong to **one fixed law** for
all selected exponents. In (4)–(5), p and x are fixed before μ is constructed,
and the conclusion is one μ with the identities for every n/k. If a protocol
changes ν, masks, p or x with the copy index k, separate applications only give
laws μₖ. Sharing the same underlying source or bank parameters does not by
itself make those laws equal, nor allow their moment entries to be pooled into
one σ or τ. A fixed p,x across the selected k is sufficient; a proof that the
varying inputs have the same pushforward law is another sufficient route.
Otherwise keep the resulting law comparisons separate. This is an application
premise, not a defect in the accepted sparse-moment theorem or finite adapter
contract.

The receiving positive-axis domain allows y=1 and y>1. If a physical supplier
also proves x(a)≤1 on positive mass, its pushforward nodes inherit y≤1. A strict
interior conclusion y<1 needs the strictly stronger physical hypothesis on every
positive-mass preimage; it does not follow merely from nonnegative durations or
the receiving type. A zero node of positive mass remains excluded by (H), while
zero-mass zero nodes cause no problem. None of these endpoint facts requires
altering the accepted CM-T02 theorem.

The exact support count is |S|, the number of distinct survival values after
positive-mass filtering. It need not equal the number of configurations, original
hybrids, copies or summands. To establish a lower bound of three nodes, for
example, one must exhibit three positive-mass indices with pairwise distinct
images, or supply an equivalent distinct-image argument. Merely exhibiting
three positive configuration masses is insufficient. This is an input check for
using the existing theorem, not a new proof or limitation of that theorem.

For the held physical supplier, instantiate p by
`configurationBankPMF ν (originalRegisterMeasure N inheritance).toPMF` and x by
`fun z => directedSurvival (maskedNormalizedTree N C H rates (masks z.1) z.2) i j`.
The original full configuration is drawn according to ν and the original bank
according to the exact supplied bank law. Correlations within ν are retained;
no product of site marginals is introduced. Hypothesis(H) must be proved from
the physical supplier rather than asserted by the abstract certificate. For
this exact held instantiation it is already supplied by
`directedSurvival_positive` applied to the same `maskedNormalizedTree`; the
companion upper-bound lemma also gives x≤1. Reuse these providers and the
positive-support helpers; no new range or support-reduction proof is needed.
Combining that input proof, (5), and `actual_randomized_legal_moment` for k>0
would give the legal-observation-to-ordinary-moment equality for this same tuple.
The construction, the physical positivity input and this equality have not been
implemented or kernel-checked here.

For any fixed application, N, calendar C, registry H, inheritance, rates, ν,
masks, original IDs and pair i/j remain the supplied shared tuple. Grouping
survival values does not redraw bits, refit rates, alter controls or change
timing. If a family of experimental rows prescribes different ν or masks, apply
the proof to each prescribed row while retaining its required common physical
source/bank parameters; do not replace them by independently fitted source
points. These are separate row laws unless their equality is proved. Even if
only x varies on one fixed p, (3)–(5) apply to each x separately; fixed p alone
does not justify pooling different x-laws into one CM moment vector. Neither
case creates a joint genealogy coupling across separately performed experiments.
Scalar pushforward laws alone do not identify the full joint weighted-tree or
forest law.

The general sparse-moment theorem in the accepted CM-T02 certificate remains
accepted at its uniform finite-positive-law scope. This derivation only supplies
the finite pushforward mathematics for a missing typed receiver. It proves no
new generator/shared-bit/semigroup instantiation of the separate CM-L02 hand
supplier, physical realization/whole-graph replacement, all-size G3/G4 closure,
effective real-algebraic algorithm or Rust refinement. The independent G7 proof
repair and all compilation/implementation ownership remain unchanged. Independent
review of this hand derivation is requested separately; no result of that review
or later formalization is assumed in this file.
