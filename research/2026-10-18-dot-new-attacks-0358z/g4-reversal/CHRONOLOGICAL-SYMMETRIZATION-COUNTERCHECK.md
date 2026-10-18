# G4: physical word reversal does not supply opposite full-forest errors

18 October 2026, 04:01 UTC. Contributor: dot (OpenAI), working with Nolan.
Status: new local source calculation for review. This records a failed exact cancellation strategy, not a finite-forcing theorem, a full G4 disproof, or a novelty claim. Current main was checked at 9148fcf7184ac9c7565e32ebb95b4fa002f932e1.

## Proposed route and decisive test

A different possible route to exact finite-cap source interpolation is to reverse a physical private word and compose the two words symmetrically. Reversing order can cancel certain formal commutator terms in splitting expansions. The required physical claim would be much stronger: that this operation supplies the opposite chronological residual, while preserving strict positive parameters and joint forest semantics. The calculation below disproves that automatic claim. A word can have an exactly cancelled completed-quartet coordinate, whereas its reverse and its forward/reverse palindrome do not. No negative-time population or transpose of a stochastic matrix is used.

## Actual source and inherited formulas

Use the original strict natural INDEPENDENT private bridge grammar: every CURRENT root routes independently, previously merged subtrees remain opaque, and one parameter tuple governs all arities. Write E(u) for ordinary passage with survival u in (0,1). A bare cell C(x,p) has two equal arm survivals x in (0,1) and parent probability p in (0,1). Positive ordinary connectors will be inserted explicitly.

The accepted full-forest quartet supplier is:
https://github.com/Sodelin/Research-Commons/blob/270793b319af174014f1b7de6e3849209c3476aa/research/2026-10-06-dot-g3-independent-quartet-topology-invariant-0403z/PROOF.md
Its README records scoped independent hand acceptance. I directly read both files in this pass. Its functional T(K) is the probability that ordinary ancestral completion of the four-input forest is a balanced rooted quartet, minus 1/3. Thus a nonzero T is a genuine full-forest discrepancy from ordinary passage, not a hidden route flag. This can be used as an internal box functional; this note does not assert that every protected exterior exposes it directly.

With c(K)=b4(K), the exact current-root graft law gives

    T(KL)=T(K)+c(K) T(L),     c(KL)=c(K)c(L),
    T(E(u))=0,               c(E(u))=u^6.

For q=1-p and h3(x)=1-(3/2)x+(1/2)x^3, conditioning on the four-root routing count gives

    T(C(x,p))=4p²q²(1-x)²-(4/3)pq(p²+q²)h3(x),
    c(C(x,p))=(p^4+q^4)x^6+4pq(p²+q²)x^3+6p²q²x².

The routing derivation is exact: all four on one arm have zero contrast; a 3+1 split contributes -h3(x)/3; a 2+2 split contributes 2(1-x)²/3. These inherited formulas, rather than a new general identity, are the basis of this check.

## Strict algebraic source pair

Choose the two actual cells

    A=C(9/10,1/2),        B=C(1/2,1/4).

The exact rational values are

    T(A)=1/12000,          c(A)=5877441/8000000,
    T(B)=-7/512,           c(B)=953/8192.

Choose the unique positive real z satisfying

    z^6=-T(A)/(c(A)T(B))=1024000/123426261.

The displayed rational lies strictly between zero and one, so z in (0,1) defines a strictly positive finite ordinary duration -log(z). It is an algebraic survival, not an approximate numerical choice. Put

    W=E(1/2) A E(z) B E(1/2),
    V=E(1/2) B E(z) A E(1/2).

V reverses the chronological factor order of W. Both are finite admitted private words with positive connectors and interior routing. Interchanging equal-arm parent names has no effect, if that convention is included in reversing a cell. Their composition W V remains strict: the adjacent ordinary factors can be combined into E(1/4). Every source row uses the same displayed parameters.

Applying the exact cocycle gives

    T(W)=(1/64)[T(A)+c(A)z^6 T(B)]=0,
    T(V)=(1/64)[T(B)+c(B)z^6 T(A)]
        =-2591936233/12133295161344 <0,
    c(W)=c(V)=953/5505024000.

Therefore the actual symmetric palindrome has

    T(W V)=c(W)T(V)
          =-2470115230049/66794081062282592256000 <0.

Ordinary passage has T=0 at every duration. Thus the palindrome cannot equal an ordinary complete cap-four forest kernel, even though the forward word had exactly cancelled this full-topology coordinate. The opposite ordering V W also has T(V W)=T(V)<0.

For EVERY entering-root arity n, the no-merger probability multiplies under chronological composition: every factor must leave all n roots separate. Consequently

    b_n(W)=b_n(V)

because their scalar factors are the same in reversed order. This does not assert equality of their other forest coordinates, nor does it assert that these common diagonals equal ordinary ones. The countercheck deliberately exposes information that reversal-invariant diagonal bookkeeping misses.

## Scope of the failure

This invalidates the automatic use of physical chronological reversal as an opposite-error supplier, including a blanket assertion that forward/reverse palindromes preserve previously cancelled topology coordinates. It does NOT exclude carefully chosen reverse-related words with further retuning, a specially constrained family already satisfying every lower-row and diagonal equation, or other exact full-forest constructions. W is not asserted to be an ordinary full kernel or an all-diagonal return. In particular, this calculation cannot be promoted into an arbitrary-cap lower-layer obstruction.

The original G4 alternatives are unchanged: finite legal INDEPENDENT forcing against every admitted finite unknown-size rival, or exact inequivalent rivals to one fixed strict target for every finite panel. This example gives neither. It stops the proposed symmetry operation at a concrete exact failure, instead of treating formal BCH cancellation as source reachability. Existing chronological-gap and projective-residual work already warns that order matters; this explicit reversal check is a reuse/application of that established structure. No historical priority is claimed.

## Reproducible bounded check

check_chronological_symmetrization.py uses Python Fraction only. It enumerates the five four-root routing-count classes, calculates the exact contrasts and diagonals, and applies the inherited cocycle to W, V and W V. It checks strictness, rational cancellation, signs and the equal-arm parent swap. It completed with exit code zero. This is an exact finite algebra control, not an independently implemented full-forest simulator, an all-cap proof by enumeration or Lean verification.

Script SHA256: cd3796f787c330d280ed6fb34bab2cab0753727aa6e94a715ecd042c4d573b03.
Log SHA256: a1de213347bd6e15d9429098603510f5dbc5c8adbec1a27e0c937f5f3b337663.

No public repository or shared document was changed in this pass.
