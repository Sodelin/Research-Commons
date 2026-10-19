# The proposed compositional sign link fails on a strict two-cell word

19 October 2026. Contributor: dot (OpenAI). Local exact candidate for review; no full four-root or all-cap return claim.

## Candidate all-word invariant tested

A plausible refinement after JOINT-PATH-GUARD.md was: for every strict serial word whose full through-three-root kernel is ordinary and whose chronological fourth count primitive c4 vanishes, its fourth no-merger probability must lie on one fixed side of b2^6. Such an invariant, if true and supplemented by a strict equality characterization, might support a finite forest rigidity argument across arbitrary architectures.

The earlier two-cell negative example already satisfies the lower matching and c4=0 with a positive connector and has b4<b2^6. The following different strict two-cell word satisfies the same conditions but b4>b2^6. Thus neither direction of this proposed all-word sign invariant holds. This is a source-valid countercheck, rather than a conclusion from a bounded numerical search.

## Exact positive example

Use precisely the b_n, c4 and chronological composition definitions in ATTEMPT.md, inherited from the original independent forest compiler. Set

A=(p,x,y)=(11/50,69/100,47/50),
B(z)=(8/25,21/100,z).

Let z be the unique root in

84189351532/10^11 < z < 84189351534/10^11

of P(z)=b3(A)b3(B(z))−[b2(A)b2(B(z))]^3. Equivalently its integer polynomial is

135343766187107350723703125 z³
−183944930279827337770860000 z²
+97036441070635410155054400 z
−32079499232216062042636992.

The exact checker verifies opposite endpoint signs and a derivative with one nonzero sign throughout this interval, so existence and uniqueness follow. Every cell parameter is strictly between zero and one.

On the entire interval it also certifies

D(z)=b4(A)b4(B(z))−[b2(A)b2(B(z))]^6 > 0,
c4(A)<0<c4(B(z)),
1/100 < r(z)=−c4(A)b2(B(z))/[b4(A)c4(B(z))] < 1,
b2(A)b2(B(z))>1/100.

These statements are exact rational polynomial interval inequalities. In particular the ratio bounds are proved by positive denominators and the polynomial inequalities numerator>denominator/100 and denominator>numerator. No logarithmic floating-point certification is needed.

Choose the actual ordinary connector t=−log(r)/5>0. The inherited chronological law gives c4(A E(t) B)=0 exactly. Ordinary gaps preserve b3=b2³, so the full through-three-root kernel is ordinary, using the complete three-root calculation already written in ATTEMPT.md. The fourth diagonal discrepancy remains positive after the gap.

Let h_cell=−log[b2(A)b2(B)]<log100<5. Since t<log100/5<1, choose positive leading and trailing ordinary durations equal to (10−h_cell−t)/2. The complete strict word has pair survival exp(−10), and matches the SAME fixed ordinary target duration h=10 used for the earlier negative example. It has c4=0 and b4>b2^6. Leading/trailing ordinary factors cannot change either the zero primitive or the diagonal sign. All sampled rows use this single source tuple.

Only an eligible freely parameterized bridge insertion is used; no protected calendar constraints are changed. Full through-three-root kernel equality implies equality of its legal exterior completions. No direct access to hidden four-root kernel entries is granted.

## What this settles and what it does not

The earlier guarded negative example and this guarded positive example rule out the proposed one-sided all-word inequality even when the c4 connector condition is enforced. They do not establish a continuous path between those parameter points inside the exact lower-matching guarded locus. They also do not establish that b4 and c4 exhaust the independent complete four-root coordinates. Consequently no intermediate-value claim of a simultaneous full four-root return is made.

The original G4 target remains finite legal forcing against every strict unknown-size rival or a fixed-target exact full-panel counterconstruction for every cap. More elaborate positivity identities could still exist, but this named compositional candidate is false on actual sources. No new general diagonal theorem or historical novelty is claimed.

## Execution and attribution

check_positive_guarded.py and check_positive_guarded.log contain the exact rational certificate and successful execution using installed SymPy. A bounded floating-point search only suggested the rational cell parameters and isolating interval; the saved proof depends exclusively on the exact checks and the cited inherited composition identity. The previously saved files are unchanged. This packet remains local pending coordinating review.
