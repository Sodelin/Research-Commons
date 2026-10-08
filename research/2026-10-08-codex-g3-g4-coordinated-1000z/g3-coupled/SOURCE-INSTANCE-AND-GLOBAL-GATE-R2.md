# Actual cubic-flat source and the unclosed global gate

Contributor: Codex correspondence lane, 8 October 2026. New hand example and exact source-definition tests. No native binary, Lean/compiler, solver, API or biological experiment was run. Independent review pending.

## 1. One strict original source and one allowed channel

Take the ordinary four-taxon rooted tree ((A,B),(C,D)), with every edge survival strictly between zero and one (choose rational one-half on frozen edges). It is finite binary, planar outer-labelled, rooted at the LSA, and cut-child vacuously. Sample four labelled A copies, one B, one C and one D. The original ancestral population completes the genealogy. There are no hybrid bits; COMMON/INDEPENDENT agree on this admitted source. All rates/lengths are positive finite, with original G3 survival coordinate x on the A pendant edge. No new calendar constraint or edge tie is supplied.

Observe a finite stochastic channel on the **final rooted labelled unranked topology**. First prune the topology to A1,A2,A3,A4,B. Let I_k(T) say that the first k A labels are monophyletic after pruning to those k A labels and B, k=2,3,4. These are deterministic functions of the final permitted topology, not hidden routing/current-root observations. Original pruning/projectivity removes sampled C,D from this readout while retaining their original source operations. This source theorem is inherited; the executable check below enumerates the complete selected five-label source law, not an independent seven-label implementation.

Only the A edge affects these probabilities. B has one selected root before A and B meet. After that meeting all selected A/B roots stay in one ordinary ancestral population until completion; intervening edge clock changes do not change its completed unranked Kingman topology, by semigroup composition with ancestral completion. Other tree edges/rates can remain any strict values. Thus the **entire** declared response depends only on x, not just on a restricted derivative with other effective directions overlooked.

The actual pure-death rates for four A roots are 6,3,1. At survival x the exact probabilities of k remaining A roots are

    p4=x^6,
    p3=2(x^3−x^6),
    p2=(9/5)x−3x^3+(6/5)x^6,
    p1=1−(9/5)x+x^3−x^6/5.

Conditional coalescent trees use actual uniform unordered current-root pair mergers, retaining the old labelled rooted trees. When k A roots meet the B root, monophyly of all k has probability 1 for k=1 and 2/[k(k+1)] for k≥2. Projectivity therefore gives

    P2=1−2x/3,
    P3=1−x+x^3/6,
    P4=1−6x/5+x^3/3−x^6/30.

These are original monophyly probabilities; no product of separately drawn forests is assumed.

## 2. Genuine stochastic channel with a cubic-flat complete response

Define the probability of channel output 1, conditional on final topology T, by

    q(T)=1/2 + [291/64 − (1971/64)I2(T)
                      + (225/4)I3(T) − 30I4(T)]/512.

It is one finite rational channel. Although its expression has negative coefficients, its actual value is a legal probability on each topology; it is not a signed source mixture. The crude sum-of-absolute-values bound already lies inside (0,1). The exhaustive 105 selected labelled-topology check gives actual range [919/2048,143/256]. The complementary output has probability 1−q(T). That identity is the only redundant response coordinate; retaining both output probabilities is equivalent to the explicit injective chart p↦(p,1−p).

Its entire observed probability is

    F(x)=1/2 + [x^6−(5/8)x^3+(9/32)x]/512.

The target p=F(1/2)=16389/32768 is rational. At that admitted interior source,

    F'(1/2)=F''(1/2)=0,
    F'''(1/2)=45/2048 > 0.

All gradients/Hessians with respect to every other ordinary source parameter vanish as well, because the channel is insensitive to those parameters. This demonstrates a genuinely singular actual-source response, beyond the regular/full-second-order local correction criteria in that presentation. It does not claim that another graph or augmented pivot presentation cannot realize p regularly.

The accepted second-order reconstruction (1835z, exact source and independent review in SOURCE-PINS) requires every nonzero annihilating covector to have kernel-Hessian negative index at least its positive corank. Here the one-coordinate response has corank one and zero Hessian, so the index is zero and that sufficient criterion does not apply. Its necessary bounded-index condition for hypothetical nonattainment is not a NO certificate. The older 2025z physical cubic-forest-direction proof concerns leading signed full-forest perturbations from actual INDEPENDENT bigons; it neither proves this final-topology channel nor a degree certificate, and retains its own attribution/status. No novelty of cubic behaviour or general degree theory is claimed.

The exact factorization is

    F(x)−p=(2x−1)^3(8x^3+12x^2+12x+5)/32768.

Hence its degree on B=(1/4,3/4) at p is +1, even though its first two derivatives at the unique root vanish. Its exact endpoint residuals are −71/2097152 and +193/2097152. This is a finite strict source degree certificate with rational boundary margin, and it supplies the actual singular instance for JOINT-DEGREE-ATTAINMENT. No source substitution, relabeling or extra observation was used.

## 3. Attempted global extension: zero local degree does not imply NO

On the SAME admitted tree and final topology readout, a second rational channel is

    q_fold(T)=1/2 + [15/8−(63/8)I2(T)+6I3(T)]/64.

Its exhaustive channel range is [13/32,271/512]. Its response is

    H(x)=1/2+[x^3−3x/4]/64,
    p_fold=H(1/2)=127/256,
    H(x)−p_fold=(x−1/2)^2(x+1)/64.

Both endpoints of the same pivot box lie above the target: residuals 5/4096 and 7/4096. This chart has degree zero although the target has the explicit strict source x=1/2. Thus degree failure cannot justify discarding a fibre, even for algebraic data and an ordinary admitted source. This is an admitted **YES** counterexample to treating this chart's degree as a necessary source certificate. It is not an all-core NO countermodel, a global nonexistence claim or a singular-NO result owned by G5.

The stronger global attempt would cover every algebraic original fibre by regular or nonzero-degree source presentations and use compactness to extract a finite witness budget. It fails at the currently unproved coverage premise: a chosen closure presentation can have zero degree, and changing it to another actual presentation is itself the original extraction problem. A compact set of closure tuples does not provide a finite open cover by degree-certified source charts without proving their existence and strict-domain margins; taking closure of a calibrated slice would additionally be invalid. Protected parameter ties may remove precisely the requisite pivot directions.

Programmed partial cut elimination gives a genuine finite core catalogue and removes every slot crossed by D. On its successor-closed surviving cuts, this degree theorem still needs a source-faithful presentation, computable full-joint face margin and coherent approximation error. No argument here bounds their actual word lengths, unknown retained multiplicities or nonphysical residual pieces. Alternative cores remain in the original problem and are not omitted. The master finite bound/terminal NO obligation therefore remains OPEN; this packet adds an honest singular positive certificate and a source-admitted failed-completeness test, not a replacement local endpoint.

## 4. Actual verification

check_degree_source.py independently enumerates every unordered Kingman current-root merger, retaining the complete labelled forest, and then the original ancestral completion. For 45 distinct rational x in (0,1), it verifies normalized positive full laws, all three monophyly formulas, both channel expectations, exact response/factor identities and channel bounds on all 105 selected labelled topologies. **762 exact checks PASS.** The receipt binds the script bytes. Polynomial identities are also shown algebraically above; finite samples alone are not their proof.

Native original pruning and generator/compiler source pins support the law correspondence but are not executed by this script. These exact tests are source-definition enumeration, not a native implementation comparison, formal proof, general source search or terminal G3 algorithm.
