# A sharp cap-four certificate for one fair private bigon

Candidate hand proof with exact arithmetic fixtures, 23 November 2026. No publication, formal kernel check, or historical priority claim.

## Scope and prior work

The original G4 asks for finite determination of each actual finite positive target by its original legal response rows, against later-inequivalent rivals of arbitrary finite size. The October 9 retained attempt "Target-relative polynomial exposure", §§3–4, identifies the already-declared SAME-source BOTH menu and the ordinary COMMON private face as a narrower test bed. It gives the equal-arm factor formula and notes that even **all** diagonal rows fail to resolve chronology. It also records the earlier accepted paired ordinary-tree certificate. We use those formulas and face setting; we do not assume all G4 menus admit private tomography, nor assume rival template equality globally.

The theorem below assumes the admissible rival class on the queried, **same matched private interface** is the strict finite E/B word grammar: ordinary populations E(z), with survival 0<z<1, and fresh current-root bigons B(q0,q1,g), with positive arm populations and 0<g<1. The word has positive leading and trailing ordinary populations in the nonordinary case. Ordinary step size is scaled to the rate-one pair coalescent. Original BOTH access **and** enough of the already-justified private tomography to recover the two COMMON diagonals and three INDEPENDENT coordinates used below are prerequisites, not new experiments. Cap four refers to entering-root arity of these kernel observables, not to a guaranteed four-taxon or five-query bound on original legal testers. Effects elsewhere in a source, transport to additional interfaces, and exclusion of alternative cores are not proved.

## Hand argument

Write C=b2_COMMON. At a common bigon the factors at arity 2 and 3 are respectively E[Q] and E[Q³], for Q=q0 or q1 with the common coin. Thus b3_COMMON≥C³, and equality forces equal arms in every bigon by strict convexity and strict interior coins (ordinary factors already satisfy equality). Henceforth work on this observable COMMON face.

For an equal-arm cell put a=1/q and h=g(1−g). Its normalized independent pair no-merger factor is 1+u, u=2h(a−1)>0. Its normalized independent triple factor is 1+3h(a²−1)=1+3u+3u²/(4h). Ordinary factors contribute one to both normalized ratios. With U=b2_I/C−1, V=b3_I/C³−1, and P(u)=1+3u+3u², we have

- 1+U=product(1+u_i), and 1+V≥product P(u_i), since h≤1/4.
- P(u)P(v)−P(u+v+uv)=3uv(2uv+u+v).

Inductively **V≥3U+3U²**, with strictness for at least two bigons, or for any biased bigon. With U>0 equality is equivalent to a single fair cell. If U=0 no bigon occurs. This is a global constraint on the stated face, independent of rival length. The optional clock upper screen uses 1+u_i ≤ (1+a_i)/2, products of these means at most (1+product a_i)/2 by (a−1)(b−1)≥0, and product a_i < 1/C because of positive ordinary duration. Hence U < (1/C−1)/2.

On the positive equality branch recover q=1/(1+2U). All ordinary populations on either side merge by their semigroup law into E(x) and E(y) with D=xy=C/q. This preserves full labelled forests, not just counts. Let K(t)=E(exp(−t)) on root counts and G its row generator G[n,n]=−choose(n,2), G[n,n−1]=choose(n,2) (n≥2). The fair B matrix is obtained by summing over k of n entering roots on the first arm with weight choose(n,k)2^(−n), running independent E(q) on each arm, and summing the two output root counts.

In descending count order (4,3,2,1) the commutator GB−BG has row 4 equal to (0,0,k,−k), with k=(1−q)³/8; all other rows vanish. Direct verification uses E(q)[2,2]=q, E(q)[3,3]=q³, E(q)[3,2]=3(q−q³)/2, E(q)[4,4]=q⁶, E(q)[4,3]=2(q³−q⁶), E(q)[4,2]=9(q−(5/3)q³+(2/3)q⁶)/5, and row sums one. These follow from the finite pure-death generator. For example, the commutator entry at row 4/column 2 is 6B[3,2]−5B[4,2]−3B[4,3]; binomial convolution gives k. The other entries follow by the same substitution and row sum cancellation.

With T=−log D, let t=−log x. At fixed T the derivative of K(t) B K(T−t) is K(t)(GB−BG)K(T−t). The derivative of its (4,2) entry is k D exp(−5t)>0. Consequently, denoting that entry by p42,

    p42 = (B E(D))[4,2] + D(1−q)^3(1−x^5)/40.

Thus p42 yields x^5 uniquely, then x as its positive fifth root and y=D/x. The physically strict admissibility test is D^5 < x^5 < 1. This identifies chronological placement in the compressed one-cell grammar. Any rival matching these coordinates under the stated interface assumptions has the same E(x)B(q,q,1/2)E(y) normal form, hence the same full private forest responses at all arities. Passing only these scalar tests for arbitrary supplied data does not by itself validate any additional supplied rows.

## Verification

Run `python3 -B g4-rh-certificate/certificate.py`. It builds root-count kernels from rational pure-death formulas and independent route convolution, then tests exact recovery, reversal detection, an infeasible transcript below the ceiling-equivalent lower envelope, an impossible chronology, and biased/two-cell controls. The recovery grid contains 36 exact rational configurations. All six tests pass, including an exact commutator fixture. The hand derivation supplies arbitrary-length validity; the tests are not a universal certificate by themselves.

## What this does not solve

- Arbitrary nonordinary targets above the sharp envelope.
- Natural INDEPENDENT-only interfaces, unproved alternatives to the matched private E/B grammar, or reuse of the same compression in arbitrary larger original cores.
- Any effective procedure for acquiring a determining transcript for every G4 target.
- Novelty relative to every historical artifact. The retained prior packet expressly distinguishes diagonal constraints from chronology, but this is not an exhaustive priority search.
