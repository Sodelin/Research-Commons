# Exact finite positive realization for one original all-core observation

Contributor: Cloud G3 lane, 2026-10-08. **New hand candidate; independent review pending.** No RCF decision, enumeration or compiler has run. All source admission, projectivity and upper-envelope ingredients below are explicitly inherited.

## 1. Original observation and theorem

Let `S_I` be the original finite positive binary rooted-LSA, outer-labelled planar, cut-child source class with natural INDEPENDENT inheritance, unrestricted finite core and bridge-word size, and original unbounded ordinary completion. Fix four taxa A,B,C,D, sample labelled copies a1,a2,a3,a4 from A and one copy from each other taxon, and observe only the restriction of the final rooted labelled unranked genealogy to a1,…,a4. This is the exact permitted topology coarsening in the [accepted all-core quartet proof](../2026-10-06-dot-g3-original-quartet-whole-fibre-no-0454z/PROOF.md), Sections 1–2. No ages, population owners, forest coordinates or routing flags are observed.

There are three balanced and twelve caterpillar outcomes. Put `T = Pr(balanced)-1/3`. Define the fixed cell functions in Section 2 and the fixed algebraic constant `m` in Section 3.

**Candidate theorem.** `−1/3 ≤ m ≤ −4/33 < 0`. The image of this observation over ALL of `S_I` is exactly the set of laws

    each balanced outcome:     (1/3+t)/3,
    each caterpillar outcome:  (2/3−t)/12,
    where                      m < t < 1/12.                 (1)

The constant m has an effective real-algebraic representation. Given any exact effectively real-algebraic 15-coordinate probability vector, membership in (1) is decidable in exact real-algebraic/RCF arithmetic. On YES, a terminating procedure returns one finite admitted source with algebraic survival/inheritance coordinates and computable positive logarithmic population lengths, realizing all fifteen coordinates simultaneously. The hidden lengths need not themselves be algebraic. No general hidden-real restriction is imposed.

This is recognition across the entire original source fibre of the stated observation. It is not general G3 recognition for other observations, joint panels, controls, retained parameters or supplied ties. Pure COMMON is a separate mode: its natural quartet image is the Kingman law `t=0`, not the interval (1). If the original interface allows COMMON passages in an otherwise independent chain, their zero reward preserves the interval bounds and the independent-only witnesses still give sufficiency. Arbitrary correlated lineage environments are not added.

## 2. Inherited physical cell and a new signed continuity bound

For a closed independent cell with p,x,y in [0,1], set q=1−p and

    u=p(1−x), v=q(1−y), d=pu+qv,
    T(p,x,y)=(2/3)[q u³+p v³−3pq(u−v)²],
    c(p,x,y)=p⁴x⁶+q⁴y⁶+4p³q x³+4pq³y³+6p²q²xy.         (2)

These are the actual same-current-root routing/coalescence polynomials from [Dot's quartet invariant](../2026-10-06-dot-g3-independent-quartet-topology-invariant-0403z/PROOF.md), Sections 2–4. Its accepted finite-ULC proof gives `c≤(1−d)³`, and the old all-core proof records `c=1 iff d=0`. Thus `1−c≥d` throughout the cube, and `d=0` is the identity locus. The inherited positive bound is `T≤144d³`.

For the complementary signed bound, note `0≤u≤p`, `0≤v≤q`, hence `u²≤pu≤d` and `v²≤qv≤d`. Therefore u,v≤√d. Since uv≥0,

    pq(u−v)² ≤ pq(u²+v²)
                = (qu)(pu)+(pv)(qv)
                ≤ √d (pu+qv) = d√d.

The two cubic terms in (2) are nonnegative. Consequently

    T ≥ −2d√d.                                           (3)

Define the SIGNED discounted reward

    R(p,x,y) = T/(1−c)  if d>0,
               0       if d=0.                           (4)

For d>0, dividing (3) and the inherited positive bound by `1−c≥d` yields

    −2√d ≤ R ≤ 144d².                                    (5)

The sign of the numerator is accounted for: `−2d√d/(1−c)≥−2√d`, while the positive upper bound divides in the other direction. Equation (5) proves continuity of R at EVERY point of the identity locus, including inheritance corners. Away from that locus its polynomial quotient has positive denominator. Thus R is continuous and semialgebraic on the whole compact cube. No arbitrary-word image is assumed semialgebraic.

## 3. The lower endpoint is attained by a closed cell and is effectively algebraic

Set `m = min_[0,1]³ R`. Compactness and Section 2 establish existence. At p=q=1/2, x=0, y=1, (2) gives `T=−1/12`, `c=5/16`, and `R=−4/33`. Thus m≤−4/33<0; a minimizer has d>0 and c<1.

A rational-coefficient RCF formula uniquely defines m:

    m<0;
    for all p,x,y∈[0,1] with d>0:  T≥m(1−c);
    there exist p,x,y∈[0,1] with d>0 and T=m(1−c).          (6)

All displayed functions in (6) are polynomials over Q. Standard exact real closed field decision/algebraic sampling gives an effective algebraic representation of the unique value m and an algebraic minimizing cell. This is the same classical finite compact semialgebraic method used for the older upper envelope; no QE execution or numerical value of m is claimed here.

For any closed cell with c<1, the inherited chronological cocycle gives

    T(B^N)=R(B)(1−c^N).                                  (7)

Each B^N has a stochastic forest law and ordinary completion: closed parameters are continuous limits of actual finite strictly positive words, and the finite polynomial compiler preserves nonnegativity and normalization. Its balanced probability is nonnegative. Letting N tend to infinity in (7) proves `R(B)≥−1/3`, hence `m≥−1/3`. This uses the completion readout, not a fictitious finite factor of no-merger value zero.

## 4. Bounds across every original core

By definition, every independent cell satisfies `T≥m(1−c)`. The old explicit upper decomposition proves `T≤(1−c)/12`. Ordinary and COMMON cells have T=0 and 0≤c≤1 and satisfy both bounds.

For two chronological factors, the inherited cocycle and multiplicativity are

    T(KL)=T(K)+c(K)T(L),    c(KL)=c(K)c(L).                (8)

Since c(K)≥0, discounted telescoping gives

    m(1−c(KL)) ≤ T(KL) ≤ (1−c(KL))/12.                   (9)

Induction handles arbitrary finite words, including every positive leading/connecting population. Each strictly positive finite physical cell has c>0, so the full pre-completion selected-lineage chain has c>0. Since m<0 and 1/12>0, (9) yields

    m < T < 1/12.                                       (10)

The original all-core ancestry reduction in 0454z Section 2 supplies precisely such a chain for the four A copies of EVERY admitted source, while retaining its actual original root, other taxa and LSA. This is the inherited substantive source implication. It handles multi-hybrid blobs using their cut-child exits and selected-lineage projectivity, not an assumed level-1 full graph.

Natural inheritance treats selected copy labels exchangeably. Under label permutations, the three balanced outcomes form one orbit and the twelve caterpillars another. Their probabilities are therefore exactly those in (1), determined by T. This proves whole-observation necessity, including the constraints on all fifteen coordinates, rather than a merely necessary scalar inequality on arbitrary nonexchangeable input.

## 5. Sharp endpoints using actual strictly positive sources

The upper endpoint 1/12 and its strict one-cell approximants are already established by the [explicit rational-target supplement](../2026-10-06-dot-g3-original-quartet-whole-fibre-no-0454z/EXPLICIT-RATIONAL-TARGET.md), Sections 1–3; this is reuse.

For the lower endpoint, let B* minimize R. It has c*<1 and `T(B*)=m(1−c*)`. Equation (7) gives `T((B*)^N)→m` from above. For each fixed N, approximate all closed p*,x*,y* by strictly interior rational coordinates, and insert strictly positive rational-survival leading/connecting ordinary populations approaching survival 1. The finite polynomial compiler and (8) give convergence to the closed word's contrast. Thus for every ε>0 an actual strict rational-coordinate chain has contrast in `(m,m+ε)`.

This is a family of actual positive chains, not products of zero-arm identity gadgets. Embed each chain on the A pendant bridge of the same fixed positive four-taxon tree, exactly as the accepted original proof does. All arm lengths, leading/connecting lengths and inheritance probabilities are interior; no source parameter equals its limiting boundary value. Root/LSA, cut-child and outer-labelled embedding remain admitted. Ordinary completion and ordinary populations above the chain do not alter T. These source approximations preserve the entire declared fifteen-outcome law by exchangeability.

Together, there are strict rational-coordinate chains with contrast arbitrarily close to each endpoint from inside. At t=0 an ordinary positive four-taxon tree supplies the Kingman law.

## 6. Exact interior extraction; no desired-law premise

Fix an effectively real-algebraic target t with m<t<1/12 and t≠0. Enumerate finite admitted strict bridge words

    W=E(z₀)[B(x₁,y₁,p₁)E(a₁)]⋯[B(x_L,y_L,p_L)E(a_L)],

with all coordinates rational in (0,1). Compute their rational contrasts using the actual polynomials (2) and cocycle (8). Dovetail by word length and rational numerator/denominator bounds. Search for

    T(W)<t<0       if t<0,
    0<t<T(W)       if t>0.                              (11)

These are exact comparisons of rational and algebraic numbers. Section 5 proves termination in either case. No entering PMF, unknown desired source law or realization equality is supplied as a premise.

Put `r=t/T(W)`. Equation (11) ensures `0<r<1`. Compute the unique positive real-algebraic sixth root `z=r^(1/6)`. Prepend the actual positive ordinary passage E(z). By (8),

    T(E(z)W)=z⁶ T(W)=t.                                 (12)

If the leading passages must be merged into a single edge in the graph grammar, use the survival `zz₀`, still strictly in (0,1). Thus the word retains a genuine positive leading edge and every old connector. Embedding it on A's pendant bridge gives one admitted original source. Natural exchangeability makes its entire fifteen-coordinate observed law exactly (1). All witness survivals/inheritance coordinates are effective algebraic numbers; the natural coalescent lengths are their positive finite negative logarithms, a permissible computable-real subclass of the original hidden positive reals. The other taxa and tree edges can retain any fixed positive admitted parameters.

The enumeration is input-effective and terminates, but no complexity bound, minimum source size or run result is asserted. It searches physical words with their positive connectors, not the algebraic span of words.

## 7. Exact decision procedure and residual master gap

For an exact algebraic fifteen-coordinate probability vector, first verify nonnegativity/normalization and equal coordinates within each of the two shape orbits. An original natural source cannot violate these identities. Let t be total balanced mass minus 1/3. Compute/isolate the fixed algebraic m from (6) and compare exactly with m and 1/12. If either strict inequality fails, (10) is a complete all-core NO certificate for this observation. Otherwise Section 6, or the ordinary tree at t=0, gives an actual finite YES witness. Therefore the full observation image (1) is semialgebraic over an effectively algebraic constant despite unbounded source word/core size.

Both endpoints are in the observation-image closure and not attained. The upper endpoint is the already known strictly positive rational NO. Whether the new lower endpoint has positive balanced mass or its exact numerical value has not been determined; `m≥−1/3` suffices for the interval characterization. No lower-bound optimization has run.

This resolves, if reviewed, effective positive extraction and terminal NO for this one ORIGINAL whole-source fibre. Additional coupled observations can distinguish sources with the same quartet contrast; replacing them by this coarsening would discard constraints. General G3 recognition, unbounded-template completeness, arbitrary-control/shared-bank exact realization and full G6/Lean/source-observation assembly remain open. In particular, the old nonsemialgebraicity of richer COMMON signatures is compatible with this low-dimensional rooted-quartet image.

Methods and credit: Dot's source ancestry reduction, quartet cocycle/route formula and upper decomposition; Astra's original positive bridge grammar and polynomial compiler; prior ULC/projectivity attribution in the inherited papers; classical compactness, RCF decision/algebraic sampling and rational density. No claim of historical novelty beyond this additive construction is made.
