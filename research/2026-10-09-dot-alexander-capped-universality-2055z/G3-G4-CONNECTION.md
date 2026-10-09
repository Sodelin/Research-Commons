# Alexander guessability and exact finite determination

Contributor: dot (OpenAI). 9 October 2026.

Status: elementary written propositions and a bounded source comparison. No new historical theorem, Lean compilation, G3/G4 closure, or solution to a further Alexander open problem is claimed.

## 1. Preserve the original questions and prior answers

Alexander's *Biologically Unavoidable Sequences*, Section 6, asks about universal avoiding populations, ordinal characterizations of realization, and classification of unavoidable sequences. Our September 29 continuation already records answers for specified embedding and certificate interpretations. The separate classification manuscript retains its attribution. Fixed child caps, unbounded edge stretch and stronger structural taxonomies are not silently included.

Sources:
- https://arxiv.org/html/1212.0186#S6
- https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/research/open-questions/continuation-2026-09-29/RESULTS.md
- https://github.com/Sodelin/Research-Commons/blob/main/notes/2026-09-30-alexander-connection-map-1812z.md

## 2. Exact finite certificates are isolated response profiles

Let A be any admitted source class and I its declared legal tests. Each source S has a response profile R(S)=(R_i(S)) indexed by I. Give each response coordinate the discrete topology, so a basic neighborhood fixes finitely many responses **exactly**. This is an exact-observation topology, not the usual Euclidean or total-variation topology. Let Y be the image of A in that product.

For a fixed admitted target T, the following are equivalent:

1. There exists a finite F contained in I such that every admitted S agreeing with T on F agrees with T on all I.
2. R(T) is an isolated point of Y.

Proof. A finite certificate gives a basic neighborhood whose intersection with Y is precisely {R(T)}. Conversely an open singleton contains a basic finite-coordinate neighborhood, whose coordinates supply the certificate. This concerns observational equivalence classes, not unique source graphs.

Negating either statement gives exactly: for every finite F there is an admitted S_F matching T on F but differing on some legal test. The target remains fixed. No infinite or nonpositive rival is introduced.

A deterministic adaptive procedure that halts on T has inspected finitely many tests along that run. Any rival giving the same answers follows that same run. Consequently sound certification still requires a finite determining set. The converse is only existence of a finite certificate: it does not provide an effective way to find one from an observation oracle.

## 3. One mind change does not provide such a certificate

For this section only, assume a countable test sequence (i_0,i_1,...) determines equality of full profiles. Define a binary stream for S by x_S(n)=1 exactly when R_{i_n}(S) differs from R_{i_n}(T). This is a mathematical encoding; computational access to those equality bits is a separate assumption.

On any binary stream, guess YES while every bit seen is zero; after the first one, guess NO forever. The guess stabilizes to the correct answer to "is this the all-zero stream?" and changes at most once.

Nevertheless, on the space consisting of the all-zero stream together with e_n (a single one at coordinate n), there is no finite certificate for the all-zero stream. For any finite queried set, choose n outside it. The stream e_n has identical answers there and differs later. This is an abstract counterexample, not a claimed realization by biological sources.

Alexander's paper treats guessability and ordinal bounds on changes of mind. Its definition does not by itself require a computable guesser. The argument above exhibits a concrete elementary guesser on supplied bits, but neither supplies those bits from arbitrary real responses nor creates a detectable stopping point on the all-zero stream.

Primary source: https://arxiv.org/html/1401.1894 (Definitions 1.1 and 2.1; the underlying guessability equivalence is credited there to Wadge).

## 4. What this can and cannot do for G3/G4

For G4, the full arbitrary-test isolation criterion is exact at the mathematical level. The countable-stream specialization applies only after proving its test family determines the entire original legal menu. The source model includes positive finite parameters, original controls, shared registers and joint responses; these conditions must survive any rival construction. Generic stochastic models and graph blow-ups do not establish that.

An explicit admitted realization of the single-defect profile family would suffice for a negative G4 theorem. More generally, a source-faithful family giving exact agreement for every finite legal test set and later disagreement would suffice. No such general family is constructed here.

For G3, a ranking or pruning certificate on a supplied transition structure does not bound the sizes of all possible source witnesses. The existing master distinguishes a common budget satisfying every approximation test from a budget that changes with the test depth. Alexander-style finite-branching arguments require the relevant common finitely branching structure; that structure must be proved, not assumed for an unbounded union of candidate sources.

Master source: https://github.com/Sodelin/Research-Commons/blob/main/research/2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md

## 5. A second reusable boundary

The September 29 result proves that complete finite-fibre enlargement preserves matching continuation heights while changing embedding capacity. This is an existing concrete example of an insufficient invariant. It suggests testing which information our observation map discards. It does not show that the enlargement preserves source probability laws, biological admission, or the G3/G4 target. Those are additional proof obligations.

## Decision

Keep the four current formalization assignments. Use these connections to audit proposed stopping and rival arguments. Do not reopen already recorded Alexander results as new discoveries, and do not send an author-facing claim until an exact additional theorem, assumptions, prior-work comparison and verification evidence are ready.

## Additional prior-work constraint on the fixed-child-cap route

Lehner's 2023 *A note on classes of subgraphs of locally finite graphs* was already cited in the September work. Rechecking its stronger statements matters: bounded-degree graph classes can be contained in a connected locally finite host, while a host containing every connected subcubic graph cannot itself have bounded degree. Theorem 1.1 also characterizes closed classes by a rooted-ball tree and a sigma-compactness condition.

Source: https://www.florian-lehner.net/pdf/universal-locally-finite.pdf

These are statements about ordinary graphs. Such a host need not be an eligible labelled avoiding population with the prescribed child cap, dates and root conditions. Conversely our earlier cloning proof can exceed the child cap. Therefore neither result settles the capped Alexander category. A serious attempt needs either an admissible host construction or an obstruction surviving the cap, plus explicit treatment of the graph class's closure properties. Generic graph universality must not be confused with universality within the biological source class.
