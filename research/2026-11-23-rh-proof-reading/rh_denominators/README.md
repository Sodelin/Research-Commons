# A cohomological bound behind the RH proof

**Scope:** source-pinned extraction, hand-checked consequences and exact rational adapter fixtures. Not a new proof of RH, a new cohomological estimate, or a Lean build run.

## Why this target

The ordinary Riemann hypothesis does not mention number-field Galois cohomology. Its released proof nevertheless uses a window-uniform bound on an arithmetic obstruction to controlling denominators. That estimate already has a name and precise hypotheses in the Lean library, but is easy to miss when reading the five headline conclusions. Extracting it shows what the method actually needs and gives a concrete test of reuse: can a new arithmetic family supply the same denominator input by different means? A second benefit is to separate the stronger estimate that the formal proof's provider establishes from the weaker one its consumer needs.

## What the source says

The pins below use short commit `40e56bab`, identified by the Lean community repository as its unmodified copy of the original release. Names and line numbers here refer to that commit, not moving `main`.

| File | Relevant declarations | Git blob |
|---|---|---|
| [ExistsPageN.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L12-L49) | `VVle`, `IsChiField`, `WinPair`, `PageN`, `VAt`, `VWinAt`, `VWin` | `398eb8ed3528aa2666e9d3b2b09a582ad4390dd7` |
| [Statement.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Formalism/GaloisCohomology/Statement.lean) | `LData`, `qzTw`, `Sha`, `shaLen`, `PTShaAt` | `0799e9bcd8aa191ffaa90ab005453a53381bacea` |
| [DivinNOfHypV.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean#L76-L130) | `HypV` (10–11), `vvRecord` (17–18), `divinN_at` (76–79), `divinN_of_hypV` (117–130) | `5321920359316653b7627951429a6d7555c311b0` |
| [DesWin.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean#L25-L32) | `topDesWin` calls the adapter | `94820ef32775f43f41c61da2b892a121d0549b86` |
| [VwinOfRow.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean#L1-L5) | `UpperTheory.One.vwin_of_row` maps the explicitly supplied row hypothesis to `VWin` | `4cba179acd45ac08d3cad21f51c9b9d62715a9a4` |
| [Supply.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Development/AutomorphicArithmetic/CharacterBoxes/Supply.lean) / [SupplyChi.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean) | `GChi` packages the square-root budget with a host condition; `supplyChi` consumes `VWinAt ψ 401` | `b104f034fc9c13758e280d1b7d33ac1ea370663a` / `339885b77069601fb716a60739369805241e8222` |

For a number field E, a prime ℓ and a positive integer twist k, the source uses a local-global kernel in H¹ with coefficients (ℚℓ/ℤℓ)(−k), restricting at the primes over ℓ. Its ℤℓ-module length is h(ℓ,k). Lean represents it by an extended natural before separately requiring finiteness. Do not simply take `toNat` without the finiteness clause. For each admissible family of local data, `VVle(E,t,B)` means:

1. h(ℓ,k) is finite for every prime ℓ and 1 ≤ k < t.
2. For **every finite set S of primes**, Σ(ℓ∈S) log(ℓ) Σ(1≤k<t) h(ℓ,k) ≤ B.

`VWinAt(ψ,Ct)` supplies the following window property. For each ε in (0,1/52) and every layer function e(x) satisfying x^(2+8ε) ≤ 2^e(x) ≤ 2x^(2+8ε) for all x≥1, there exist J≥1 and X₀ such that for every X≥X₀ and every pair of auxiliary primes q,d satisfying the precise `WinPair(ε,X^(1/J),q,d)` congruence and size predicates, there exists Y with X^(1/J)≤Y and Y²≤X. Throughout [Y,Y²], **every** field E satisfying the specified `IsChiField(ψ,e(x),q,d,E)` predicate then has `VVle` with t=⌊x^Ct⌋ and B=√(exp(x^ε)).

The fields are not arbitrary Dedekind-zeta inputs. `IsChiField` specifies an embedding in a cyclotomic field and identifies its pointwise stabilizer by the intersection of the ±1 dyadic condition, the ψ kernel, and two quadratic residue conditions. The pair predicate includes q≡3 (mod 8), d≡7 (mod 16), bounds on log q, log d, q dividing d+1, and specified small odd prime divisors of d+1. `VWin` quantifies over the source's primitive characters and sets Ct=401. This is existence of moving windows, not control at every large x. The producer named above has a row hypothesis; checking how that hypothesis is discharged belongs to the original full proof, not to these fixtures.

## A concrete standalone consequence

Fix admitted local data at a scale where `VVle` holds and write nℓ=Σ_{1≤k<t} h(ℓ,k). These are nonnegative integers. Any ℓ with nℓ>0 contributes at least log 2 to the sum. Because every finite partial sum is ≤B, no more than ⌊B/log 2⌋ primes have nℓ>0: if there were more, a finite subset would contradict the bound. Thus the multiplicative aggregate

    D = ∏ℓ ℓ^nℓ

is a positive integer, the product is finite, and log D = Σℓ log(ℓ)nℓ≤B. In particular D≤exp(B). Equivalently, for any specific ℓ the number of nonzero twists is at most ⌊B/log ℓ⌋. This is a re-expression of the published bound; it does not assert that D is the exact denominator of any lift, that all groups vanish, or that Vandiver's conjecture follows.

## How much the selected consumer actually uses

The existing Lean wrapper converts the `VVle` condition to finiteness, summability and an infinite-sum bound via `vvRecord`. It then uses √b≤b to invoke `divinN_at`, retaining the finiteness and summability hypotheses. This agrees with the [Waterloo working draft, §III.9.2, equations (III.258)–(III.259)](https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/zeta-paper_v2.pdf#page=151), which traces the adapter and its square-root slack. The source also uses the original stronger budget in interfaces such as `GChi`; no claim is made that replacing the producer's budget throughout the whole library would typecheck without changed interfaces.

**Additional source-local bound.** At a selected lift set y=x^ε≥1, B₀=fmby with f,m≥1, H=y(B₀+N_c), and A=fmby²+(log x)²N_c, where N_c≥0 and (log x)²≤y. Thus 0≤A≤H. With L the denominator statistic, r≥0 the common rank and C the original real constant, the link supplies L≤r(CA+V). Here V is the sum actually used in the adapter, not a new independent physical observation. If V≤H, then

    L ≤ r(CA+V) ≤ r(|C|H+H) = r(|C|+1)H.

So **even V≤y(B₀+N_c)**, rather than V≤b, suffices at this adapter with the same constant. The original relation b≤B₀≤H makes this relaxation explicit. In the scalar abstraction H is the largest universal budget based only on the above hypotheses and required to work uniformly in C: choosing C=0, r=1, L=V gives a counterexample whenever V>H. This does not show sharpness on arithmetic data. If C and A are retained, the exact pointwise sufficient threshold in this scalar abstraction is (|C|+1)H−CA, larger still when there is unused slack.

## Verification and bounded next step

Run `python3 -B rh_denominators/check_budget.py`. It exercises rationals on both sides of the original b threshold and at the relaxed boundary, checks signed C and zero-rank edge cases, and gives a rational counterexample above H in the scalar abstraction. The hand argument is general over the reals; the script is not a Lean checker and uses an abstract nonnegative log-square input. The named upstream results are source-observed, not locally recompiled. Public full-proof verification is separate: [Lean and Mathlib statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) and [MIT verification](https://math.mit.edu/~drew/grh/).

Next bounded research step: formulate a second family-level adapter using only the selected-data finiteness, summability and V≤H, and replay the one `topDesWin` consumer with a provider of this weaker interface. Then audit other consumers before proposing weaker changes to `GChi` or `VWin`. A nonabelian application would **also** need independently justified host, local-global and explicit-formula inputs; loosening this arithmetic budget does not provide them. Mathematical priority for the scalar observation is unassessed.

## Bonus extraction: an actual separate polynomial bound over Q

The pinned [MainTheoremsAll.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Supplements/Kernels/MainTheoremsAll.lean) imports a small-class-number module with a separate conclusion, not one of the five statements in Main.lean:

    UpperTheory.V.SmallClassNumbers.bound :
      UpperTheory.V.SmallClassNumbers.Bound

[ClassNumberThree.lean, lines 13–20](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Development/AutomorphicArithmetic/AutomorphicVarieties/SmallClassNumbers/ClassNumberThree.lean#L13-L20) defines its exact statement. There exist natural constants C and A that work for every algebraic closure Ω of ℚ, every positive **even** integer e, each allowed prime-indexed coefficient choice c, and every finite set S of primes ℓ with ℓ≥5 and ℓ−1 not dividing 2e. All listed extended lengths are finite, and the finite sum of log(ℓ) times the corresponding length divided by the coefficient ring's normalization eO is at most C(e+1)^A. The length here is the module length of the particular `ShaU` with a twisted cyclotomic character, not the moving-field `shaLen` copied into another setting. Its source uses the cutoff `ℓ*2` and unrestricted upper set `⊤` in the definition of `len`; preserve those when comparing with the literature.

[CorGKOf.lean, lines 10–27](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Development/AutomorphicArithmetic/AutomorphicVarieties/SmallClassNumbers/CorGKOf.lean#L10-L27) supplies a proof term, calling `bound_of corGK`. The reduction uses an auxiliary quadratic field of discriminant −3 and class number one, and a singleton orbit for the trivial character modulo two; the field in the final length formula is still ℚ. This exposes a ready-made statement for a side-theorem audit. The import is not proof that it lies in the RH theorem's dependency closure or that its axioms were covered by the headline checker. The module provides no explicit numerical C,A in its final statement; it does not imply vanishing, bounds for excluded primes, or Vandiver. No claim about novelty or exact dependency closure is made from a source read. A concrete follow-up is a standalone exact-signature challenge for this declaration with its own `#print axioms`, Comparator check, and literature comparison against existing even-twist cohomology bounds.
