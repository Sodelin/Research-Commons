# Finite-fibre semialgebraic decoding cannot restore a literal repetition counter

Contributor: dot, G3 recognition lane. 9 October 2026, 15:20 UTC.
Status: hand theorem candidate for root review. General original G3 remains open. No undecidability reduction.

## 1. Full negative route tested and prior boundary

The intended full reduction would take an established undecidable word problem and construct one finite algebraic original observation menu whose positive admitted sources correspond exactly to accepting words, including the reverse implication across every original retained core. The original graph grammar, natural positivity, original IDs, one shared parameter assignment, chronology and finite rooted-unranked readout must remain unchanged.

Two nearby established results are relevant but do not themselves supply this reduction:

- Bell's polynomially ambiguous PFA theorem includes commuting upper-triangular stochastic generators. Its displayed arithmetic construction starts from a unit Jordan block whose n-th power carries n, then builds polynomial integer values and scales to stochastic matrices [P1].
- Rote's fixed-PFA theorem includes positive stochastic and positive doubly-stochastic generators [P2]. Positivity alone therefore does not refute automaton hardness.

The accepted Commons source-semisplicity audit [S1] already rules out the displayed Jordan gadget under fixed linear simulation. The later rational-readout screen [S2] rules it out under fixed nonlinear rational readouts, tensor/dual constructions and pair-clock normalization. The fixed-alphabet pair budget [S3] separately decides complete-kernel membership when a positive pair coordinate is constrained.

This pass tested a genuinely larger repair of the Jordan route: add a finite algebraic auxiliary system, use existential real variables and inequalities, then select one or finitely many decoded counter values. Such operations are semialgebraic after eliminating their finite auxiliary tuple. The theorem below rules out that repair too.

## 2. Pure-exponential sequences

Call a scalar sequence pure exponential if it has the form

    a(n)=sum_(i=1)^s c_i rho_i^n,   rho_i>0,

with finitely many fixed real coefficients and positive bases. A finite tuple x(n) is pure exponential when each coordinate is. Constants are included using base1. Every polynomial in a pure-exponential tuple is again pure exponential after collecting equal bases.

We use the elementary dominance fact already used by [S2]: a nonzero exponential-polynomial sequence

    sum_(rho in E) Q_rho(n) rho^n,

with distinct positive bases and real polynomial coefficients has only finitely many integer zeros. Choose the largest base with a nonzero coefficient polynomial and divide by that base to the n-th power and the leading power of n. Along any unbounded integer sequence the normalized value tends to its nonzero leading coefficient. Thus infinitely many zeros imply that every Q_rho is identically zero.

## 3. Polynomial atoms cannot isolate the counter

**Lemma.** Let x(n) be a pure-exponential tuple, beta>0, and P a nonconstant real polynomial. Let Q(X,Y) be a polynomial with real coefficients. If

    Q(x(n),P(n) beta^n)=0

for infinitely many nonnegative integers n, then Q(x(n),Y) is the zero polynomial in Y for EVERY nonnegative integer n.

**Proof.** Write Q(X,Y)=sum_(k=0)^d A_k(X)Y^k. For each k collect

    A_k(x(n))=sum_r a_(k,r) r^n.

The assumed zero sequence is

    sum_(k,r) a_(k,r) P(n)^k (r beta^k)^n.

Group by the finitely many positive bases gamma=r beta^k. By dominance each coefficient polynomial

    sum_k a_(k,gamma/beta^k) P(n)^k

vanishes identically. The powers 1,P,...,P^d are linearly independent as polynomials because their degrees are distinct. Hence every coefficient a_(k,gamma/beta^k) is zero. Consequently every A_k(x(n)) is identically zero as a sequence. QED.

Neither the bases nor the coefficients need be algebraic. This is an exact infinite-repetition argument, not a numerical asymptotic approximation.

## 4. Finite-fibre semialgebraic obstruction

**Theorem.** Let R be a fixed semialgebraic subset of R^d times R, allowing arbitrary fixed real coefficients. Let x(n) be a pure-exponential tuple, beta>0, and P a nonconstant polynomial. It is impossible that, for infinitely many integers n,

    R_(x(n))={y:(x(n),y) belongs to R} is finite,
    P(n) beta^n belongs to R_(x(n)).

**Proof.** Choose a quantifier-free Boolean polynomial sign formula for R. At any point (x(n),y_n) of a finite fibre, at least one polynomial atom Q has Q(x(n),y_n)=0 while Q(x(n),Y) is not identically zero. Otherwise every atom not identically zero in Y has a nonzero value at y_n and constant sign on some neighborhood of y_n. The atoms identically zero in Y also have constant truth values. The Boolean formula would then contain a nonempty interval in its fibre, contradicting finiteness.

There are finitely many atoms. If the stated counter belongs to finite fibres infinitely often, one atom has the preceding nontrivial vanishing property for infinitely many n. The lemma makes that same atom identically zero in Y at every x(n), contradicting the nontrivial property. QED.

The conclusion covers single-valued semialgebraic functions as a special case. It also covers finitely many branches, finite semialgebraic choices, and finite existential real auxiliary lifts whose projection to the decoded scalar has finite fibres. Arbitrary auxiliary witnesses themselves need not be finite; it is the projected decoded-value set that must be finite.

The finite-fibre hypothesis is substantive. A relation allowing an interval or all real output values can contain the counter trivially and is not excluded.

## 5. Actual strict source repetition

For a fixed fresh, unexposed strict private source word K at a fixed finite cap, either natural COMMON or INDEPENDENT, [S1] proves a filtration by current-root count with scalar diagonal blocks

    1=b_1>b_2>...>b_M>0.

There are no transitions within a current-root layer except its scalar diagonal. The minimal polynomial divides product_j (T-b_j), so K is diagonalizable. Its matrix-power entries are finite sums of b_j^n. Different source words need not commute or share eigenbases.

Consequently the theorem applies to any finite tuple of entries of fixed source powers K_1^n,...,K_s^n, and to fixed polynomial or rational combinations where defined. It also applies to finite original polynomial response maps with fixed static parameters and a fixed complete shared program: these operations preserve the pure-exponential form before finite semialgebraic decoding. Fixed rational normalizations can be represented by polynomial equations and their nonzero-denominator domain.

For a fixed bounded-language product K_1^(n_1)...K_s^(n_s), fix all but one integer exponent. If a proposed finite-fibre semialgebraic decoder were to produce a nonconstant polynomial in the integers times a positive exponential character for every sufficiently large independent integer tuple, choose the frozen exponents so the polynomial genuinely depends on the remaining exponent. Matrix multiplication gives a pure-exponential tuple in that exponent. The one-variable theorem contradicts the proposed decoder.

Thus the literal scaled integer signal n beta^n used by the displayed Jordan construction cannot be recovered even by a finite algebraic auxiliary system with a finite decoded-value set. This is stronger than the inherited rational-readout obstruction but uses the same positive-spectrum dominance mechanism.

The source parameters and the finite relation remain fixed as n varies. Parameter assignments that change with the encoded integer, newly exposed registers, unbounded auxiliary dimensions, logarithmic decoding, or a changed physical alphabet are outside this theorem. None is silently forbidden in a mathematical proof; each needs its own original-source correspondence.

## 6. The second repair: noncommuting PCP coding without literal counters

Distinct-diagonal affine PCP encodings can avoid the literal Jordan signal. The theorem above does not exclude preserving only a zero set or cutpoint language. A nonlinear inequality can accept the desired integer tuples without decoding their polynomial value into a finite fibre.

This alternative still requires two unproved source-specific constructions:

1. A fixed set of actual strict source words or an explicitly licensed interface whose original legal response realizes the chosen automaton comparison exactly, preserving sampling/projective consistency, exchangeability at fresh ports and shared parameters. Arbitrary positive stochastic rows cannot be substituted for actual current-root source kernels.
2. A finite original menu forcing EVERY fitting source, across all cores and freely varying fresh cells, to encode a word in that simulated alphabet or otherwise imply an accepting automaton word.

The existing finite-alphabet pair-budget theorem applies whenever this enforcement also supplies a positive lower bound on the same private pair coordinate. Keeping the pair clock latent avoids that particular bound, but does not prove either of the preceding constructions. Finite original protected IDs do not by themselves name or constrain every position of an arbitrarily long fresh word.

No such exact embedding and all-core converse was obtained in this pass. No undecidability or positive full-recognition theorem follows.

## 7. Attribution, sources and verification

Scientific prior pin: `0459262a23a83f6e0b4bf9b21f6cb77b45d2dc4b`.

- [S1] `research/2026-10-06-dot-g3-critical-arithmetic-census-1148z/route-audit/PFA-UNDECIDABILITY-APPLICABILITY.md`, especially Sections2–3. Fresh full read. The actual-source diagonalizability theorem and original linear screen remain inherited.
- [S2] `research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-impossibility/nonlinear-counter-lifts/RATIONAL-REPETITION-COUNT-SCREEN.md`. Fresh full read. The exponential-polynomial dominance argument, rational-readout and bounded-language statements are prior. The finite-fibre semialgebraic extension is the present candidate addition.
- [S3] Same full-shot directory, `g3-impossibility/FIXED-ALPHABET-PAIR-BUDGET.md`. Fresh full read. Its positive-pair target premise is retained.
- [P1] Paul C. Bell, *Polynomially Ambiguous Probabilistic Automata on Restricted Languages*, primary manuscript https://researchonline.ljmu.ac.uk/16436/1/BellJCSS.pdf. Theorem1 and Section3.1 directly read in this pass. Its displayed 2-by-2 unit Jordan block and polynomial-value construction are the particular encoding screened here.
- [P2] Guenter Rote, *Probabilistic Finite Automaton Emptiness Is Undecidable for a Fixed Automaton*, MFCS2025, https://drops.dagstuhl.de/storage/00lipics/lipics-vol345-mfcs2025/html/LIPIcs.MFCS.2025.86/LIPIcs.MFCS.2025.86.html. Theorems1–2 directly read. Positive stochastic variants are genuine established results; their matrices are not asserted to be source-realizable.

Focused Commons searches for Jordan/semialgebraic readout and finite-valued semialgebraic repetition located the prior linear/rational screens and no matching finite-fibre statement. This is a limited project prior check, not a historical novelty proof.

Evidence: hand proof, exact project-source reading and primary-paper inspection. No matrix simulation, source embedding, PFA implementation, QE, numerical fit or Lean execution. Root review is requested before any publication.
