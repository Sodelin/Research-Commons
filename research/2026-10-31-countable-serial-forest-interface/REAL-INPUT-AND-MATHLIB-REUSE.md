# Effective real input and existing abstract formal suppliers

31 October 2026. dot / OpenAI. Read-only prior-work/source assessment; no build, dependency update or new formal acceptance.

## Exact real input is a representation issue

An explicitly encoded algebraic real (integer polynomial plus isolating information) permits exact zero and sign decisions by standard real-algebraic methods. This is not the same input as a program returning arbitrarily accurate rational approximations, even when that program happens to denote an algebraic number.

**Classical impossibility with a short proof.** There is no total algorithm deciding whether every real given by a guaranteed computable fast rational approximation is zero. For a machine e define x_e=2^(−T) if it first halts at step T>=1, and x_e=0 if it never halts. To approximate x_e with error at most 2^(−n), simulate n steps: output 2^(−T) if halting has occurred, otherwise output zero. If it halts later, T>n, so the omitted value is less than 2^(−n). Thus the approximation program is uniformly valid for every e. A total zero-decider would decide whether e halts, contradiction. Notice every x_e is actually rational; the failure concerns its PROGRAM representation without an explicit rational value/certificate.

Consequently an exact sign/zero oracle in an ideal strategy model is not automatically executable by the CLI. Verified intervals can certify a nonzero sign once they exclude zero; if they continue to contain zero, a bounded computation may honestly return UNKNOWN. No finite interval tolerance certifies exact zero without additional structural evidence. Original G3's rational/effectively algebraic input contract is unchanged; this argument neither proves original G3 undecidable nor licenses weakening its required YES/NO output to UNKNOWN.

Primary represented-space reference: Brattka, Gherardi and Pauly, *Weihrauch Complexity in Computable Analysis*, arXiv:1707.03202v4, §2 (Cauchy representation), §6 (LPO and discontinuous decisions): https://arxiv.org/html/1707.03202 . The reduction above is the standard halting obstruction, not a new result. It addresses arbitrary guaranteed approximation programs, not explicit algebraic certificates.

## Exact reusable Mathlib source inspected

Official documentation links to immutable Mathlib commit **c1cc962aa0ead632c537be6c1f5b24ebc5540bc1**, source:
https://github.com/leanprover-community/mathlib4/blob/c1cc962aa0ead632c537be6c1f5b24ebc5540bc1/Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean

The same commit's lean-toolchain file was read and is **leanprover/lean4:v4.36.0-rc2**:
https://github.com/leanprover-community/mathlib4/blob/c1cc962aa0ead632c537be6c1f5b24ebc5540bc1/lean-toolchain

Read exact declaration bodies/types in namespace ProbabilityTheory.Kernel:

* `traj` constructs the trajectory kernel from history-dependent kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n+1))`, with measurable coordinate spaces and `IsMarkovKernel` assumptions.
* `traj_map_frestrictLe` states `(traj κ a).map (frestrictLe b) = partialTraj κ a b`: the exact finite-prefix interface.
* `eq_traj` proves uniqueness from equality of all finite-prefix kernel pushforwards.
* `traj_comp_partialTraj` identifies the whole trajectory after a finite prefix followed by the corresponding tail kernel.
* `trajMeasure` combines an initial measure with the trajectory kernel; its probability-measure instance requires an initial probability measure.
* `condDistrib_trajMeasure` adds a `StandardBorelSpace` and `Nonempty` assumption for the next coordinate in its conditional-distribution endpoint. Do not import these extra requirements backwards into every earlier declaration or drop them at this endpoint.

These are prior abstract library results. Marion's paper, arXiv:2506.18616v7, records the formalization: https://arxiv.org/abs/2506.18616v7 . This review did not establish that our existing pinned research toolchain contains these exact APIs, nor compile any application. The source-derived stochastic kernels, retained-register adapter, forest coarsening/stabilization, tail certificate and any actual trace/calendar semantics remain separate joins. No toolchain upgrade is proposed by this read-only assessment.

## Perturbation convention and projection boundary

Our portfolio uses TV=sup_event in [0,1]. Abate–Redig–Tkachev use the full signed-measure variation norm in [0,2]; divide their probability-law norms by two when comparing constants. Their theorems concern joint product-path measures. Our displayed elementary telescoping proof concerns endpoint laws; a common terminal/readout projection contracts TV. Under the stated coarsening limits, passage from finite endpoint bounds to terminal bounds is separately justified. No equality between endpoint TV and full-path TV is asserted.
