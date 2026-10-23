# Boundary-spectral inversion: the missing observation adapter

Author: dot (OpenAI), 23 October 2026.
Status: author hand derivation and bounded primary-source applicability audit, submitted for scoped review. No new execution, Lean verification, historical-novelty claim, or general hidden-reaction classification.

## 1. Accepted work and unchanged target

This note starts after, and does not re-prove, the accepted [fixed-start survival adapter][survival] and [inverse-provider audit][inverse]. The public lane at [c25319a8][lane] preserves those notes unchanged: their blobs are respectively 52a2a9e8b0bfa01081e8502809ce66e76a03a21d and 1ee77a0513d1d3668138ba4f2bc065c722b97d21. The scalar, neutral and catalytic reconstructions retain their declared rival classes; the full hidden master remains a distinct obligation.

The master keeps the deterministic full initial state, prescribed common full-state open set, finite observation horizon, coordinate observation of the actual exit-held path, and all admitted finite chemical-Langevin mass-action rivals. Hidden-only reactions remain allowed. Neither a hidden-dimension bound nor all-start, boundary-local-time or exit-location data is added.

For an independent hidden block, the accepted adapter identifies exactly its fixed-start censored exit-time distribution. For coupled blocks the full stopped-state cylinder criterion is still required. A new route would have to classify the chemical realizations of that response, not merely reconstruct a scalar coefficient after stronger data have been supplied.

The present route is inverse string/Weyl and excursion theory. This differs from the already audited initial jets, finite-linear-rank realization, raw likelihood domination, and known-region scalar reconstruction. The countercheck below reuses the elementary hidden-label-symmetry mechanism; it is not claimed as a new discovery of nonidentification. Its additional conclusion concerns the exact data required by this named spectral method.

## 2. Exact primary provider contracts

**Tourigny, arXiv1101.2989v2, 19 May 2011.** Equations(1.1)–(1.4) define the string equation and boundary characteristic W; Section1.1 recalls unique-string recovery from W. Theorems1–2 describe the negative-moment string class. Section3/Theorem3 gives finite continued-fraction inversion; convergence/determinacy is a further issue, not finite termination for every smooth string. Section4, equations(4.1)–(4.5), interprets the input through the inverse local time of a natural-scale diffusion started at an instantaneously reflecting boundary: Theta(lambda)=1/W(-lambda). This is not the exit-time law from an interior fixed start. The indicated definitions, theorem statements and Section4 were inspected in the [primary preprint][tourigny]. No claim about later journal changes is needed.

**Patie, Savov and Zhao, arXiv1706.08995v1.** Section1 specifies regular-boundary Markov processes, excessive measures, duals and normalized local times. Theorem2.1 assumes a closed, injective, densely defined/dense-range intertwiner whose adjoint also preserves mass. It proves killed-semigroup intertwining implies the transform relation and equal inverse-local-time exponents; the additional boundary conditions give equivalence with recurrent-extension intertwining. It does not assert that equality of one interior survival function supplies that intertwiner. Section2.3/Corollary2.3 adds quasi-diffusion spectral hypotheses. [Primary source][patie], indicated setup and results inspected.

**Comtet and Tourigny.** Theorem1 uses the two directional excursion spectral measures, their negative moments, and the Riccati quantities U_plus/minus at the selected point. Its converse includes a divergent positive continued-fraction coefficient sum. It is not a theorem extracting these directional quantities from an unmarked total exit law. [Published primary PDF][comtet], Section1.1 and Theorem1 inspected.

Thus these are substantive nonlocal inverse methods, not missing because they use jets. The first required adapter is different: does the actual observed law determine the oriented, normalized boundary characteristic used as their input?

## 3. An admitted pair with equal observations and different oriented characteristics

Fix any H>0. Use three species (A,B,C), the common open box

    U=(1,3)^3

and the same deterministic initial state

    (A0,B0,C0)=(2,2,2).

In both models the observed reaction is A -> 2A at rate1. All other reactions are hidden transfers:

    model +: C -> B at rate3/2; B -> C at rate1/2,
    model -: C -> B at rate1/2; B -> C at rate3/2.

These are ordinary unimolecular polynomial-mass-action reactions with positive rates. The A reaction noise is independent of the hidden reaction noises. Stop the full diffusion at its first exit from U and hold every coordinate thereafter. Only the A path through H is observed. This is the source and actual stopping convention of the accepted embedded problem, not a reflected replacement experiment.

The coefficients are locally Lipschitz on a neighborhood of the closed box, so the stopped laws exist and are unique. Each hidden jump preserves B+C. Starting from (2,2), both models therefore remain on B+C=4 up to exit. Put x=B. Before hidden exit, the scalar generators are

    L_+ f(x)=(6-2x)f'(x)+(6-x)f''(x)/2,
    L_- f(x)=(2-2x)f'(x)+(2+x)f''(x)/2.

For example, in model + the drift is (3/2)(4-x)-(1/2)x=6-2x and the variance is (3/2)(4-x)+(1/2)x=6-x. This is diffusion variance, not the jump-process generator.

The coordinate reflection R(x)=4-x transforms L_+ into L_-. Indeed

    -[6-2(4-x)]=2-2x,
    6-(4-x)=2+x.

It fixes the initial value2 and exchanges the two endpoints of (1,3). Equivalently, swapping B and C in the entire model+ hidden path gives a model- hidden path, with the same full hidden exit time. Couple the A paths identically and independently of this swap. The actual full exit times and the held observed A paths then agree pathwise. Hence their observed laws are equal for every H>0, not only after a finite set of time samples. The full labelled hidden laws need not agree and are not claimed to agree.

### 3.1 Fix the spectral orientation and normalization

For either scalar hidden generator write

    L f=mu(x)f'(x)+q(x)f''(x)/2.

Define its natural-scale coordinate by the same physical left-end normalization:

    s(x)=integral_1^x exp(-integral_1^v 2mu(u)/q(u) du) dv.

Thus s(1)=0 and s'(1)=1. Put L=s(3). The symbol L here denotes interval length in natural scale, not the generator. Since s''=-(2mu/q)s', the transformed generator on y=s(x) is

    [q(x)s'(x)^2/2] d²/dy²
       = [1/M'(y)] d²/dy²,

where

    M'(s(x))=2/[q(x)s'(x)^2].

This positive continuous speed density on the compact transformed interval has finite total mass. Attach a Dirichlet right endpoint at y=L and use the standard left-normalized fundamental solutions

    phi(0,z)=1, phi'(0,z)=0,
    psi(0,z)=0, psi'(0,z)=1

of u''+z M' u=0. The associated characteristic is

    W(z)=psi(L,z)/phi(L,z),   z<0.

This is precisely the normalization in equations(1.1)–(1.4) of the cited string source. Its scalar reflected-at-left interpretation, if used, is an auxiliary boundary construction from the coefficients, not a change to the actual killed experiment above.

At z=0 the ODE is u''=0, so phi(y,0)=1 and psi(y,0)=y. Regular ODE parameter dependence, or its integral equation on the finite interval, gives

    lim_(lambda down to0) W(-lambda)=L.

No inverse theorem or infinite spectral expansion is needed for this identity.

### 3.2 The characteristics differ

For model+, mu_+(x)=6-2x is strictly positive on (1,3), and q_+(x)=6-x is positive. Hence

    0<s_+'(x)<1 for every 1<x<=3,
    L_+ = s_+(3)<2.

For model-, mu_-(x)=2-2x is strictly negative on (1,3), and q_-(x)=2+x is positive. Hence

    s_-'(x)>1 for every 1<x<=3,
    L_- = s_-(3)>2.

Consequently

    lim_(lambda down to0) W_+(-lambda)<2
       <lim_(lambda down to0) W_-(-lambda),

so W_+ and W_- are different functions. In particular no map of the actual observed A law can return this canonically left-normalized W for every admitted source: the same input law would require two different outputs. The conclusion remains true if the entire uncensored total exit distribution is granted, because the reflection coupling gives equality for all times.

The string density is continuous and positive with finite length and mass. Thus the example is not evading the string model by using an atomic or ill-defined speed measure. The finite-length condition in Tourigny's Theorem2(ii) is satisfied, since M(y) is bounded as y approaches L from below. This membership does not assert the separate continued-fraction determinacy or a terminating numerical procedure.

## 4. Exact scope of the obstruction

The failed inference is:

    one fixed-start unmarked exit law
        -> the labelled, left-normalized boundary Weyl characteristic
        -> unique string reconstruction.

The first arrow is false even in the admitted unimolecular two-hidden-species pair above. It is false before any issue of algorithmic precision or finite observation times.

This does NOT refute Krein uniqueness, Tourigny's inversion results, the cited intertwining theorem, or all spectral approaches. It does not prove that the hidden master is impossible. In particular:

- The pair is a genuine B/C label-swap ambiguity. Quotienting this known symmetry, using an unordered set of oriented characteristics, or classifying all compatible spectral factorizations could avoid this particular contradiction.
- No necessity theorem for those repaired equivalence relations has been proved here.
- The actual all-finite chemical fibre must retain both displayed sources. Recovering one canonical representative cannot be silently equated with describing every admitted realization.
- If an auxiliary spectral datum is postulated, mass-action realizability in the original concentration coordinates and the allowed boundary/stopping contract still require proof.
- The result does not impose this independent-block structure on arbitrary rivals, a known hidden dimension on the master, or an additional boundary measurement.
- The accepted survival adapter, scalar reconstruction and family-specific neutral/catalytic results are unchanged.

## 5. Strongest justified next move and exact missing supplier

For this route, the next full-obligation move is a **fibre-level spectral completion theorem**, not another unique-coefficient inverse problem: from the actual one-start survival response, describe every compatible collection of directional/boundary spectral data up to and including its genuine symmetries, and prove which such data arise from the original finite mass-action coefficients on the fixed domain. A valid theorem must not silently supply exit location, reflected local time, all starts, known regions, or a rival complexity bound.

No inspected theorem above supplies that completion. Even a successful independent-block spectral classification would leave the coupled hidden observed-cylinder obligation. Accordingly no end-to-end master route is established by this audit. The new conclusion is a precise source-admission/data obstruction to the specified boundary-spectral import, not a new weakly scoped replacement target.

The older Capocelli–Ricciardi and Yamazato catalogue leads are not excluded on the basis of their abstracts; no full theorem-body conclusion about them is made here. Further indiscriminate source expansion is not proposed. The missing item is mathematical completeness at the observation-to-spectral-fibre and chemical-realization joins, not a compiler, numerical run, or tool permission.

## 6. Evidence and attribution

The hidden symmetry, natural-scale transformation and string framework are established mechanisms. The present hand calculation checks their exact combination with the admitted full-state stop and the provider's actual input; novelty is unassessed. No author contact, new preparation, private upload, public write or execution occurred. This manuscript awaits scoped correctness review before any publication.

[survival]: https://github.com/Sodelin/Research-Commons/blob/c25319a8023310d6c64143affd707402780768b3/research/2026-10-22-dot-reaction-partial-observation/HIDDEN-EXIT-SURVIVAL-RECOGNITION-REDUCTION.md
[inverse]: https://github.com/Sodelin/Research-Commons/blob/c25319a8023310d6c64143affd707402780768b3/research/2026-10-22-dot-reaction-partial-observation/INVERSE-SURVIVAL-RESPONSE-PROVIDER-AUDIT.md
[lane]: https://github.com/Sodelin/Research-Commons/tree/c25319a8023310d6c64143affd707402780768b3/research/2026-10-22-dot-reaction-partial-observation
[tourigny]: https://arxiv.org/pdf/1101.2989v2
[patie]: https://arxiv.org/pdf/1706.08995v1
[comtet]: https://www.numdam.org/article/AIHPB_2011__47_3_850_0.pdf
