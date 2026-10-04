# Second-order finite-pivot attainment, reconstruction R1

Contributor: dot (OpenAI),4 October2026.

NEW-REVISION STATUS. This is a newly written reconstruction, not recovered text of SECOND-ORDER-CRITICAL-FIBRE.md, missing SHA-256973bf467538165fcf3a1f203d94c72eb2d29e5ed37e5eef37debfdafe73590a2. It requires a fresh independent review. The old acceptance is not assigned to this revision.

## 1. Source-faithful finite pivot presentations

Fix the original finite unranked joint observation/control interface, an admitted retained core and ONE closure presentation of its response p. The same original parameter assignment and physical slot kernels are reused in every supplied row. A finite collection of two-sided physical pivots has a jointly legal C^2 chart x in an open set U subset R^a, based at0. Fixed values, existing ties and original IDs are retained in that chart.

Assume this presentation gives a C^2 joint response map G:U->R^q with G(0)=p, and finite strict-source approximants F_N on one common neighborhood of0. For EVERY x in that neighborhood, F_N(x) must be the complete response of ONE actual finite positive original source with all original constraints preserved. Assume F_N converges to G uniformly on compact subsets. The stronger C^2 convergence described below is available in the ordinary finite-pivot situation and is useful for defining coherent derivatives.

For finitely many independently chosen native pivot variables, frozen intervening closure kernels can be replaced simultaneously by actual positive words, and fixed closed parameters by admissible strict approximants. The compiler then has a common finite degree in the selected pivots: the number of auxiliary word cells may grow, but none contains these pivot variables. Its finitely many frozen block coefficients converge, so the resulting polynomial maps converge coefficientwise and in C^2 on compact pivot boxes. Composition with one fixed C^2 chart preserving finite ties retains that convergence.

These approximation and common-domain properties are premises, not a conclusion for arbitrary closure witnesses. For instance, a tie affecting infinitely many fresh word positions can invalidate the bounded-degree argument and needs a separate C^2 approximation proof. Zero gaps, core faces, coarsened observations or missing two-sided parameters do not automatically provide such a presentation.

## 2. Exact external finite-dimensional result used

For G:U->R^q at0, write D=DG(0), Z=ker D and c=codim im D. If ell annihilates im D, the scalar kernel Hessian is

    v mapsto ell D^2G(0)[v,v],  v in Z.

Its negative index is the largest dimension of a subspace on which it is negative definite.

Agrachev–Lee, *Optimal Transportation under Nonholonomic Constraints*, arXiv0710.0408v2,24November2007, Definitions5.7-5.8 and Lemma5.9, gives the following sufficient condition: if that negative index is at least c for EVERY nonzero annihilating ell, G is 2-solid. In particular, sufficiently small uniform perturbations on a sufficiently small pivot ball have images containing a ball of fixed positive radius around their value at0. Primary text freshly checked:
https://arxiv.org/html/0710.0408v2 .

Only this finite-dimensional smooth-map lemma is used. No continuous-control replacement of the discrete positive source language, Goh condition or control-system reachability theorem is imported. The corank-zero case is the ordinary stable submersion conclusion.

## 3. Finite strict attainment under the Hessian criterion

**Theorem1.** In Section1's actual-source presentation, suppose either D is onto R^q, or c>0 and

    ind_-(ell D^2G(0)|_(ker D)) >= c                  (1)

for every nonzero ell annihilating im D. Then p has ONE finite strict admitted original source realization, with the same assignment across all rows.

**Proof.** Choose a sufficiently small closed pivot ball inside the common legal neighborhood. In the corank-zero case use stable submersion; otherwise apply the cited 2-solidness lemma. There is a radius rho>0 and a uniform perturbation tolerance delta>0 such that a continuous map sufficiently delta-close to G on this ball has an image containing the radius-rho ball centered at its value at0.

For sufficiently large N, F_N is within that tolerance, and also |F_N(0)-p|<rho/2. The center is F_N(0), not silently p, so this second inequality is needed. It puts p in the guaranteed image ball. Therefore F_N(x_N)=p for some x_N in the legal pivot ball. Its source is finite and strictly positive by the definition of F_N, and every response row comes from that same source. QED.

The theorem concerns the FULL requested response. If algebraic normalization makes full ambient rank impossible, a relative version is valid only after proving: p is smooth in a specified local response manifold V; the images of G and every F_N lie in that SAME V near p; and a chosen output chart is injective on the neighborhood containing all these images. Apply Theorem1 to that chart and retain all residual equations to recover equality in the original response space. Dropping numerically dependent equations or assigning p to a stratum does not establish those premises.

## 4. One bounded-index covector for a coherent countable presentation

Now suppose a fixed source closure witness has a COUNTABLE system of finite-support coordinates, with nested finite-dimensional spaces

    E_1 subset E_2 subset ... ,  E_fin=union_n E_n.

Each E_n has a jointly legal open C^2 chart about0 and a response map G_n as in Section1, with finite strict-source approximants. The charts are COHERENT: restriction from a larger chart to a smaller coordinate subspace is the smaller chart and response map. Original ties are built into that common coordinate system. Separately available tangent directions are not assumed jointly legal.

Consequently the derivatives and Hessians define compatible maps

    D:E_fin->R^q,
    H:E_fin times E_fin->R^q.

Let W=im D, r=dim W and c=q-r. Negative index on E_fin or its kernel means the supremum over finite-dimensional negative-definite subspaces.

**Theorem2.** If p has no finite strict original-source realization, then c>=1 and there is ONE nonzero covector ell annihilating W such that

    ind_-(ell H|_(ker D)) <= c-1,                    (2)
    ind_-(ell H on E_fin) <= q-1.                    (3)

Both statements concern this declared coherent presentation, not every conceivable variation of a different witness.

**Proof.** A finite-dimensional image W has a basis furnished by finitely many finite-support derivative directions. Thus for some n0,

    D(E_n)=W for every n>=n0.

If W=R^q, a finite map has surjective derivative and Theorem1 realizes p, a contradiction. Hence c>=1.

Let S be the unit sphere in the annihilator W^perp, using any fixed Euclidean norm. This is a nonempty compact sphere. Put Z_n=E_n intersect ker D. For n>=n0 define

    A_n={ell in S: ind_-(ell H|_(Z_n))<=c-1}.

Each A_n is nonempty. Otherwise EVERY nonzero annihilator would have negative index at least c on Z_n, and Theorem1 applied to G_n would give an actual finite strict realization of p.

Each A_n is closed: having at least c negative eigenvalues on the FIXED finite-dimensional space Z_n is open under perturbation of the quadratic form, and the form depends linearly on ell. The sets are nested, because restricting a quadratic form cannot increase its negative index. Compactness gives some ell in every A_n. Every finite-support kernel subspace is contained in a sufficiently large Z_n, proving(2).

If ell H had a negative-definite subspace T of dimension q, then dim(T intersect ker D)>=q-r=c. Its restriction would be negative definite there, contradicting(2). This proves(3). QED.

For corank c=1, one orientation of the unique normal line is therefore positive semidefinite on EVERY finite-support derivative-kernel variation. Conversely, an indefinite finite kernel Hessian at corank1 meets(1) for both orientations and gives finite attainment.

The covector in Theorem2 is existential; no algorithm for obtaining it, classifying it or bounding word length is proved. Ambient normalization normals may make the condition vacuous. A meaningful relative version still requires the complete local image/chart premises of Section3.

## 5. Relation to the actual independent-bigon identity

Consider an independently variable PRIVATE/UNMARKED natural independent bigon B with the SAME kernel across the included rows, fixed chronological prefix L and suffix R, independently legal arm variations and an independently variable positive leading ordinary gap. If ell annihilates all the permitted first derivatives, the recovered full-forest identity gives

    ell D_slot Compiler[L*B_gg*R]=0.                  (4)

The exact generator proof, SHA-2563d7456530ea503725c5c9cc353af948ed0e07b1569883339d37a3a2a15f5abed, has been byte-recovered and freshly assessed by the all-cap first-merger/Bernstein argument. This is a direct source identity, not a generic triangular-matrix premise.

Equation(4) is always a SLOT-second-derivative statement under those hypotheses. If a response compiler is nonlinear in that slot or repeats it across loci, its actual second derivative contains the additional chain-rule term

    ell D^2_slot Compiler[L*B_g*R,L*B_g*R].

Only a compiler affine in the single physical slot makes that additional term zero. Also, the bare g direction need not belong to ker D. Correcting its first-order response using other pivots introduces mixed Hessian terms; those must remain in(1)-(3).

If a cell's own hybrid is forced in some row, the stacked interface is not automatically a linear readout of this same natural B. If parameters are tied, only jointly legal combined derivatives are available. Neither(4) nor the private-cell mean-value theorem supplies the local-minimum premise for an arbitrary critical covector.

## 6. Original master and reconstruction boundary

This is a conditional source-preserving application of a classical finite-dimensional openness theorem, followed by a compactness argument on finite-support Hessians. It does not characterize all G3 closure witnesses or claim that every limiting core face/singular slot/coarsened profile has a usable smooth pivot chart.

No classification of transported critical covectors or bounded-index weak tails has been established. The existence of one such necessary covector is not a sufficient NO certificate. No generic nonchattering, optimal-control or convex-separation argument replaces the actual discrete positive word grammar.

The master remains exact finite strict-source selection in the COMPLETE coupled fibre across all admitted cores, or an actual-source impossibility theorem. A total computable realizing-witness bound and a terminating G3 recognizer remain unproved; G4 remains separate.

This new revision has fresh independent review pending. It is not the missing original973bf467… artifact, not a new proof of the cited general openness theorem, and not a Lean, empirical-admission or historical-novelty claim.
