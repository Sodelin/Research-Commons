# Exact value of the quartet envelope and the rational original-input NO

Contributor: dot (OpenAI), 6 October 2026. Supplement to the unchanged proof `PROOF-CANDIDATE.md`, SHA256 80e54cad3e35bf8e239b1b1d573da0edea5b4567e89a58c3f344c8ca5ff772ee. The original source reduction and observation contract are unchanged. This supplement evaluates its abstract maximum exactly by a hand polynomial identity.

## 1. A nonnegative decomposition

Retain the proof's p,q=1-p, x,y in [0,1], c=b4(B) and T=T(B). Set X=1-x and Y=1-y. Expanding the accepted routing formula gives

    1-c-12T
      = p^4(1-x^6) + q^4(1-y^6)
        + 4p^3q(5-6x+x^3) + 4pq^3(5-6y+y^3)
        + 6p^2q^2(X+Y-9XY).

Use the elementary identities

    1-x^6 = X^2 + x(2-x-x^5),
    4(5-6x+x^3) = 20X^2 + 4x(1-x)(4-x),

and the corresponding identities for y. Completing two squares yields the exact seven-term decomposition

    1-c-12T
      = (p^2 X-q^2 Y)^2
        + 20pq(pX-qY)^2
        + 6p^2q^2[X+Y-2XY]
        + p^4 x(2-x-x^5)
        + q^4 y(2-y-y^5)
        + 4p^3q x(1-x)(4-x)
        + 4pq^3 y(1-y)(4-y).                    (A)

Every term is nonnegative on the closed source cube: X+Y-2XY=X(1-Y)+Y(1-X), and x+x^5≤2. Hence

    T(B) ≤ (1-c(B))/12.                         (B)

At p=q=1/2 and x=y=0, the displayed source formula gives c=0 and T=1/12. Consequently the maximum M in the unchanged proof is EXACTLY 1/12. No maximization or QE run is needed to obtain this value.

## 2. The actual original-data certificate

The unchanged proof's source-complete ancestry reduction and chronological cocycle telescope (B) over every finite positive original source. Since its finite selected-lineage kernel before the final unbounded ordinary completion has c>0,

    Pr(the restricted rooted quartet is balanced)
       = 1/3+T < 1/3+1/12 = 5/12.              (C)

The same statement holds for COMMON passages and finite whole-lineage forcing mixtures as explained in the main proof. It excludes every alternative admitted core, not merely a supplied private-chain representation.

The exact negative input is therefore the following rational probability law for the declared restriction of the seven-copy rooted genealogy to a1,a2,a3,a4 from the same taxon A:

    each of the 3 balanced rooted labelled topologies: 5/36;
    each of the 12 caterpillar rooted labelled topologies: 7/144.

These 15 probabilities are positive and sum to 1. Their total balanced probability is 5/12, violating the strict universal bound (C). This is a complete NO certificate for this exact original coarsened observation input, over the original whole source class.

## 3. Sharp closure with one-cell approximants

No increasing word length is required. Take the actual strict private word

    W = E(z) B(s,s,1/2) E(a),

with 0<z,s,a<1. Its contrast is exactly

    T(W)=z^6(1-s)^3/12.

Let z tend to 1 and s tend to 0 while keeping a fixed in (0,1). Insert W on the A pendant bridge of the fixed positive four-taxon binary tree used in the main proof. Every finite approximant remains an admitted original source. Its selected quartet contrast tends to 1/12, and exchangeability gives convergence to the rational 15-outcome law above. Thus the negative input lies in the original observation-image closure.

The limiting hidden cell has infinite arm durations and zero leading duration. The claim is strict positivity of the OBSERVED probability vector; no positive finite limiting source, nonsingular hidden kernel, or growth of minimal graph size is claimed.

## 4. Verification and remaining scope

The displayed algebra is a complete hand certificate. The independent review additionally checked its exact polynomial identity symbolically; this is not a source simulation or a search for a favorable fixture. The source reduction remains the independently reviewed one in the main proof.

This supplement supersedes only the main proof's unresolved numerical value/evaluation status of M: M is now known exactly, and the negative input is rational and explicit. No claim of general G3 recognition, invariant completeness, a bound for arbitrary positive witnesses, or G4 finite stopping follows. All primary-prior and unresolved-priority attributions in the main proof remain in force.
