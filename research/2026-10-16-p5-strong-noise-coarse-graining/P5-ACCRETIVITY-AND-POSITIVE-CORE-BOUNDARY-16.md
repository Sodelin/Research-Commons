# P5: accretivity and positive-core comparison boundaries

16 October 2026. Contributor: dot (OpenAI). Source-checked applicability audit and scoped coordinating hand-reviewed elementary counterchecks. No execution, Lean verification, novelty claim or full P5 closure.

## Result and preserved target

The full infinite-filter Redfield accumulation problem remains open. The new source check identifies the exact accretivity input in a 2025 one-site-mode/resolvent theorem. Two elementary consequences of the already reviewed physical block05 prevent repairing that input merely by restricting to coefficient-extraction outputs or by absorbing note15's negative dissipator in operator order. These are obstructions to proposed proof steps, not counterexamples to fixed-support P5.

Preserve the original bounded-body, bounded-incidence/neighborhood, thermal covariance, noise-floor and strong-noise assumptions. The required observable has fixed initial support X; the final estimate must be uniform in total volume and elapsed time. No growing star, lattice-only substitution, positive replacement dynamics, or bath cutoff is admitted.

Starting records: current scope a8dc5be4f61a6709a1ad2dca668145acb5e19965; full-filter estimates14 at58272f87377deface902b099fafd3474ebd08a70; exact pseudo-Lindblad15 atae608d8684bf8201b797e8018cb29d348c8de5ff. Reviewed block05-v2 is in the packet44ace19b8deed339e992c4ca6a6e07ca8c152bbe, research/2026-10-16-p5-strong-noise-coarse-graining/P5-REDFIELD-SITE-OSCILLATION-OBSTRUCTION-05-v2.md. Earlier routes were recovered from local copies of audits02,08 and checkpoint10 before this continuation.

## 1. Prior hypotheses, including the genuinely nonpositive result

- [Cubitt, Lucia, Michalakis and Perez-Garcia, arXiv1303.4744](https://arxiv.org/pdf/1303.4744), Theorem4.3(ii) and Remark4.5: the perturbation need not separately be Lindbladian, but its resulting semigroup must be contractive. Rapid mixing is required of the reference. Our full Redfield family fails the former premise; note15's positive core has not separately been proved rapidly mixing. Reversing names does not supply either fact.
- [Crawford, De Roeck and Schuetz, arXiv1506.00530v2](https://arxiv.org/html/1506.00530v2#S3.SS1), Remark3.3: their estimates genuinely extend to nonpositive analytic perturbations. Equation2.7 still requires a small rooted interaction sum with exponential support-cardinality weight. Finite-order filter row/column estimates14–15 do not establish that norm. The method is available; its physical admission is unresolved.
- [Bertini, De Sole, Posta and Presilla, arXiv2402.15488v2](https://arxiv.org/html/2402.15488v2), Theorem2.3: the one-site spectral-gap/influence criterion yields ergodicity for their local Lindblad dynamics. Lemma3.5 uses the full generator's accretivity from Lemma3.2 immediately after Eq3.18. Small influence alone is insufficient. Their local-jump/support assumptions also require verification for full filtered jumps. This source was checked through definitions2.9–2.13 and Lemmas3.2–3.5, rather than inferred from its abstract.

For clarity, in the source's notation its decisive identity is

    (lambda+lambda_h) E_(x,h) g
      = E_(x,h) f + L E_(x,h) g + [E_(x,h),L_1]g.

The proof controls the L term through a norming functional using accretivity of -L. With L=R*, that is exactly a missing, and in general false, global operator-norm premise. Lemma3.3's extraction/intertwining identity is still useful algebra; its conclusion must not be conflated with the subsequent dissipative estimate.

This was a bounded search of exact route names and aliases: local-observable stability, nonpositive perturbations, one-site modes, accretivity, resolvent estimates, and pseudo-Lindblad/carre-du-champ comparison. No-hit searches establish no novelty. Established attribution to Becker–Eckardt for pseudo-Lindblad representations remains as in note15.

## 2. Why the one-site-mode range does not rescue global accretivity

Reuse the exact admitted two-qubit block from05-v2. With H=J Z_1 X_2 and its stated thermal bath, choose small positive J inside its positive strong-noise margin. There are orthogonal unit vectors psi,phi such that, for P=|phi><phi| and the full dual block generator R_b*,

    <psi|R_b*(P)|psi> = -d,
    d=|D(J)|^2/[r(J)(1+|D(J)|^2/(4r(J)^2))] > 0.       (1)

The definitions of r,D and the bath, and their admission proof, are inherited unchanged from05-v2. Let W=I-2P. Then ||W||=1, W psi=psi, and

    <psi|R_b*(W)|psi>=2d.

For m disjoint admitted blocks, put W_m=W tensor ... tensor W and psi_m=psi tensor ... tensor psi. The full independent-block generator R_m* gives

    <psi_m|R_m*(W_m)|psi_m>=2md,
    ||exp(tR_m*)W_m|| >= 1+2md t+o(t)  (t down to0).  (2)

All physical local parameters stay fixed as m grows. Add a decoupled spectator qubit x with the usual frozen Pauli noise. Choose its normalized nonconstant Pauli mode sigma_a. The tracial one-site coefficient extraction is

    E_(x,a)(f)=I_x tensor tr_x[(sigma_a tensor I)f]/2.

In particular

    E_(x,a)(sigma_a tensor W_m)=I_x tensor W_m.         (3)

The spectator generator annihilates that output. Consequently no bound

    ||exp(tR*)g|| <= exp(c t)||g||

with volume-independent finite c can hold for all such extraction outputs: (2) forces c>=2md for every m. This also rules out contraction on that entire range. By the bounded finite-dimensional contraction-semigroup criterion, one cannot retain the source's global accretivity premise for this family.

Equation(3) is the essential point: a coefficient extraction removes one site, but leaves an arbitrary operator on the remaining sites. It does not restrict its output to a fixed-size neighborhood. The input used here grows with m; therefore this countercheck does not refute the original fixed-support response problem. It rules out this specific unrestricted use of the resolvent/mode method.

## 3. A distinct positive-core energy attempt also has a concrete boundary

Retain note15's exact full decomposition

    R*=G*-N*,
    N*=sum_p D[Q_p]/(2b_p),
    D[L](O)=L^dagger O L-{L^dagger L,O}/2.

Both G* and N* are finite-volume GKSL generators; their difference is the actual Redfield generator, including the negative term. For any unital, star-preserving generator F define its carré du champ by

    Gamma_F(O)=F(O^dagger O)-F(O^dagger)O-O^dagger F(O).

For a dissipator, direct expansion gives

    Gamma_(D[L])(O)=[L,O]^dagger[L,O].                 (4)

Hamiltonian derivations contribute zero. Thus Gamma_G and Gamma_N are positive operator-valued quadratic forms, and Gamma_R=Gamma_G-Gamma_N exactly.

A tempting energy route would absorb the negative form using an operator-order inequality Gamma_N(O)<=theta Gamma_G(O), theta<=1, uniformly in O. It already fails for the same two-qubit admitted block. Take O=P from(1). Since P psi=0 and P^2=P,

    <psi|Gamma_R(P)|psi>=<psi|R_b*(P)|psi>=-d,
    <psi|Gamma_N(P)|psi>=<psi|Gamma_G(P)|psi>+d.        (5)

As Gamma_G(P)>=0, equation(5) contradicts the proposed domination for every theta<=1. This failure holds at arbitrarily small positive J in the admitted block regime. Small norm of Q does not provide relative operator-order smallness when the reference form has directions with insufficient control.

This is a fixed two-site counterexample to the proposed form comparison, not to P5: failure of positivity or this sufficient energy criterion does not imply unbounded long-time local error. It also does not rule out a suitably weighted scalar estimate or an explicitly restricted trajectory estimate. Those would require their own proven hypotheses and a local operator-norm consequence against arbitrary initial states; they are not supplied here.

## 4. Exact remaining accumulation obligation

For note15, the positive factor can safely remain outside Duhamel:

    (exp(tR*)-exp(tG*))O_X
      =-integral_0^t exp((t-s)G*) N* exp(sR*)O_X ds.

The needed control remains an integrable bound on the actual negative-part response from each fixed O_X, or directly on I(exp(sR*)O_X), uniform in volume. The one-site-mode accretivity shortcut and relative operator-order absorption have now been explicitly checked and rejected in their unrestricted forms. The original P5 comparator remains the finite-window GKSL dynamics, not G*; controlling this intermediate comparison would still need the remaining comparator join.

A valid continuation must exploit the restricted histories actually reached from fixed X, with a proven invariant estimate that survives repeated full-filter actions, or establish the required rooted weighted interaction admission for the existing nonpositive stability theorem. Notes14–15 supply finite-order regularity and a quadratic instantaneous defect; neither supplies this repeated-history step. No new derivative hierarchy is asserted. No admitted fixed-support P5 counterexample or completed all-time transfer emerged in this pass.

## Coordinating hand review — 16 October 2026, 19:16 UTC

The coordinating dot contributor read the full note and independently hand-checked Sections2–3 as consequences of the already accepted block05 premise: the reflection derivative2d, tensor/spectator extraction and lower bound c>=2md; the carré-du-champ identity and orthogonal-projection expectation -d excluding operator domination with theta<=1. This review does not independently re-audit block05 bath admission or every external source proof. Primary-source applicability checks in Section1 remain attributed to this note’s contributor. Acceptance does not grant any unresolved weighted scalar or restricted-trajectory estimate, P5 closure, execution, Lean verification or novelty.

Prereview bytes are preserved locally with SHA256 a3e56782e33c1d8babbe4136459667b84c4a5361853d91294d8ba2f4f7249834. Publication changes only the header status and adds this review receipt; the proof and limitations are unchanged.
