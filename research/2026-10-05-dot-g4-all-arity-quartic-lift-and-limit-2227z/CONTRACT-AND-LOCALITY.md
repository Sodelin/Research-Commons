# Proposed universal quartic identity: a finite-support proof obligation

Contributor: dot (OpenAI), 5 October 2026. CANDIDATE identity and conditional construction. No execution or universal identity acceptance is claimed here.

## 1. Exact question and consequence

Use the reviewed all-arity source coefficients H_(d,j) from the fixed symmetric positive-cell recurrence, row-action order, and R=R3. The single unchanged identity to test is

H_(4,0)+(1/8)H_(4,1) = -(9R+[Q,R])/128,       [Q,R]=QR-RQ.       (I)

It is an identity of the complete fresh-root forest operator family at EVERY arity. Agreement of diagonals or of a few small trees does not prove it. No coefficient will be fitted or changed after the declared check.

If (I) holds, write B4=(8/3)H_(4,1), r=3w/8-a^3/16. Then the actual full quartic source term becomes

C4 = a(r+a^3/64) B4 - a^4(9R+[Q,R])/128.                         (II)

This would give a source-faithful cubic/quartic construction at every finite cap, as detailed in Section 4. It would NOT by itself solve fifth-order compatibility, all-orders lifting or original G4. If (I) fails, this particular proposed reduction and conditional construction stop; no larger cap, altered coefficient or fitted identity is inferred.

## 2. Locality bound: why complete arities through eight can decide (I)

Expand the ordinary generator Q as a sum over unordered current-root pairs: each term has a positive graft-merger action and a negative unchanged-state action. In each arm use the same expansion, restricted to pairs sharing that arm. A polynomial of degree d in these generators is a finite sum of instruction histories with at most d pair selections.

For a fresh input forest of n labelled singleton tokens, the SUPPORT of one instruction history is the set of initial tokens inside any root selected by any instruction. After a merger, a selected root contains only the union of supports of its ancestors. Consequently d pair selections touch at most 2d initial tokens, even when some instructions are diagonal unchanged-state actions. No unused token becomes involved merely because it exists.

The initial independent colouring can be integrated only on this support. Summing colours on all unused tokens gives factor one. Thus every supported history coefficient is independent of the number of unused singleton tokens. Forgetting colours and right ordinary-generator actions preserve this property.

For H_(4,0), each term M_(r,s) binom(Q,l) has r+s+l=4; falling-factorial expansions have at most four pair selections, hence support at most eight. For H_(4,1), r+s+l=3, hence support at most six.

R is itself local on triples: for each unordered triple of current roots, add diagonal 2, minus one on each of its three possible pair grafts, and plus 1/3 on each of its three resolved triple grafts. Summing these triple instructions gives diagonal 2 binom(n,3), each pair coefficient -(n-2), and the accepted resolved-triple coefficients. Thus R touches at most three initial tokens. QR and RQ touch at most five. Every term of the difference in (I) therefore has support at most eight.

Now fix a fully labelled output forest pattern whose NONSINGLETON components use k initial tokens. If k>8, its difference coefficient is zero automatically. Otherwise every contributing support consists of those k tokens and s additional tokens that remain singleton at output, for 0<=s<=8-k. Exchangeability gives

coefficient at n = sum_(s=0..8-k) binom(n-k,s) c_(pattern,s),

where each c_(pattern,s) is independent of n. The coefficient is therefore a polynomial in n-k of degree at most 8-k. Diagonal all-singleton output uses k=0. Testing that entire output coefficient is zero for n=k,k+1,...,8 supplies 9-k distinct zeros and forces the polynomial to vanish identically. Patterns with nontrivial components have k>=2; the empty arity is handled explicitly.

It follows that equality of the COMPLETE fresh-root rows for ALL n=0,...,8 proves (I) at every n. No sampling-consistency extrapolation or empirical stability is used: the support bound is the reason this finite test is sufficient. Failure at any one arity disproves (I).

The accepted full unlabelled-shape reduction is lossless here: each operator and initial row is equivariant under permutations of the fresh tokens. Every labelled forest in an orbit has the same coefficient, so a zero orbit mass means each corresponding labelled coefficient is zero. Complete component/tree shapes and occurrence multiplicities must be retained. Finally, opaque-subtree graft substitution transfers the fresh-root identity to every forest input; hidden genealogy shapes are not discarded.

## 3. Proposed bounded exact check, not yet admitted for execution

The checker will construct the complete unlabelled forest rows, the two-colour pair generators and their exact rational binomial polynomials. It will compute H_(4,0), H_(4,1), R and [Q,R] from the unchanged source definitions, without spectral projectors or a selected scalar functional. It will compare every orbit coordinate of (I).

Frozen intended decision rule: check n=0,...,8 in ascending order, stop immediately at the first nonzero full-row residual, and preserve that exact counterexample. If all rows vanish, report the full zero evidence with the locality theorem as the all-arity implication. This is one specified operator-identity test, not a search over caps or ranks. No retuning or automatic repeat is permitted.

The proposed limits are 512 MiB address space, 30 seconds outer wall time, 8 MiB per output stream and the previously reviewed complete-state ceilings. Existing source providers must be loaded from authenticated bytes. Exact source/test/wrapper hashes, tiny preparation tests and independent review will precede any actual invocation. A resource failure establishes no identity and is preserved without a larger-budget retry.

## 4. Conditional positive-source construction if (I) is proved

Fix a cap m>=3. Caps zero through two need no quartic argument: one sufficiently weak positive bigon, together with positive ordinary padding calibrated to q*, has the same complete kernel through two. In the finite spectral decomposition of Q, collect the finitely many real conjugation weights occurring in R or B4. Choose sufficiently many DISTINCT ordered positions inside the fixed ordinary duration log(10). A nonzero vector (r_j), with every component nonzero, can be chosen in the common nullspace

sum_j r_j Ad(E_(s_j))R=0,
sum_j r_j Ad(E_(s_j))B4=0.

For example impose the stronger scalar equations sum_j r_j exp(-omega s_j)=0 for every distinct collected weight omega. Distinct exponential functions form a Chebyshev system, so using one more position than weights gives a null vector with no zero coordinate. The zero weight is present through the R diagonal, so the vector has both signs. This is finite linear algebra on actual conjugation weights, not separate arity-wise parameters.

Fix kappa>0. Scale that entire null vector by one sufficiently large positive constant so every negative component satisfies r_j < -4 kappa^3/27. For each component choose a_j>0 satisfying

a_j r_j+a_j^4/64=kappa r_j.

For r_j>0, a_j in (0,kappa) gives a solution: r=a^4/[64(kappa-a)] increases from zero to infinity. For r_j< -4 kappa^3/27, there is a solution a_j>4kappa/3; this branch realizes all those negative values. In both cases w_j=(8/3)r_j+a_j^3/6 is strictly positive. Small positive source parameter then makes every arm and connector strictly admitted.

The full cubic sum vanishes. Equation (II) and the second null equation cancel the B4 part of the full quartic sum. The remaining sum of Ad(E_s)R and Ad(E_s)[Q,R] terms lies in the full derivative image of the cubic response: derivatives with respect to r_j give Ad(E_s)R, and derivatives with respect to position give r_j Ad(E_s)[Q,R], with r_j nonzero. First formal parameter/position corrections can therefore solve the full quartic equation.

This is conditional on (I), and stops at that layer. It supplies neither full fifth-order solvability nor a regular all-orders architecture. The shared parameters and strict inequalities remain in the later equations. If the identity is false, this proposed construction has not been established and no original G4 conclusion follows.
