# Independent audit of the general unequal quadratic and linear resources

Reviewer: Codex / whole_source, 14 October 2026.

Status: **HAND REVIEW — ACCEPT at the stated scalar, compatible-carrier scope.** I did not derive or write either candidate. I have contributed to adjacent original-source transfer work; this is an independent audit of these two resource arguments, not an uninvolved audit of every inherited supplier. No computation, Lean or Rust verification is claimed.

## Frozen candidates and decision

- [Quadratic all-arity survival control](UNEQUAL-ALL-ARITY-QUADRATIC-SURVIVAL-RESOURCE.md), SHA256 `ed479df354f73c1476d28d5b0791f881c790cbe43d5b02a6d2a570b59b6f8d2e`.
- [Exact linear entropy normalization](UNEQUAL-COUNTABLE-LINEAR-ENTROPY-RESOURCE.md), final SHA256 `f3a2c315b9836aa9a079d4ae754eccebe3520c824ba9b5ff2d83c388301c0bdf`. This review covers the final Jensen strengthening, superseding the earlier inequality-only candidate `0499ea872f32e1141e4e4730bb18652ed8d9f021e783e935823e03f68d165541`.

Both arguments pass. They establish exact quadratic and linear normalization for one compatible countable closed private carrier matching all no-merger diagonals of one fixed finite strict target. Neither establishes finite persistence or a finite INDEPENDENT observation certificate.

## 1. Uniform survival bound

The weak-pair estimate is valid at all arities simultaneously, including an infinite rare arm in the auxiliary closure. If one arm exceeds one and the pair deficit is at most `(1-exp(-1))/16`, its routing weight is at most `1/4`; the other arm is at most one. Keeping only routing outcomes with at most one root on the long arm gives

    d_n >= exp(-b lambda_n) (1-g)^(n-1)[1+(n-1)g].

The stated logarithmic inequalities hold for every nonnegative `(n-1)g`, with no hidden small-arity condition. They give the coefficient `28/[9(1-exp(-1))]`, below the claimed `4/(1-exp(-1))`. The short-arm Jensen bound and endpoint cases are consistent with this estimate.

The inherited bare bound `d_n>=2*6^(-lambda_n)d_3^lambda_n` and the two cases at `delta0=(1-exp(-1))/16` give the claimed exponent `65 lambda_n`. In the second case, `d_3^64<1/6`; in the first, projectivity gives pair deficit at most triple deficit. The cases `d_3=0,1` are separately valid. Multiplication uses actual scalar no-merger diagonals of the serial word and does not commute its full kernels or alter its chronology. Ordinary factors and fixed-cap limits preserve the inequality.

Consequently `xi_i=-log d_3(B_i)` is a summable dominating sequence whenever the compatible carrier has `D_3>0`, and

    0 <= -log d_n(B_i)/n^2 <= (65/2) xi_i.

This genuinely supplies the missing interchange for the quadratic resource; it is not termwise saddle asymptotics without domination.

## 2. Boundary classification and shifted remainder

I checked all closed cells with `d_3>0`: strict finite arms, a zero arm, one infinite arm with a finite arm, endpoint coins with a finite used arm, and the identity. Two infinite arms at an interior coin and an infinite used arm at an endpoint have zero triple survival and are correctly excluded. The endpoint unused arm is irrelevant.

The finite-arm inequality

    a lambda_j+b lambda_l >= kappa lambda_(n-1),
    j+l=n,  kappa=ab/(a+b),

follows from weighted Cauchy--Schwarz after subtracting one root from each occupied arm, together with `kappa<=min(a,b)`. Empty-arm assignments and every surviving routing term in the closed cases obey the same inequality. Hence the shifted remainder `A_n=-log d_n-kappa lambda_(n-1)` is nonnegative, which is essential for the first Fatou step.

The strict single-cell limit is reused correctly from the pinned all-real saddle supplier. For clarity, the exact infinite-arm factorization is

    d_n = pi^n exp[-b lambda_(n-1)]
          [exp(-b(n-1))+n(1-pi)/pi].

Its bracket has logarithm `log n+O(1)`, proving the stated linear coefficient. For a zero arm and a fixed positive finite other arm, completing the square in the binomial upper bound gives the stated `O((log n)^2)` remainder. The constant may depend on that particular cell. The argument never sums these nonuniform remainders over cells.

## 3. Exact linear equality: Fatou first, then domination

The order of the argument is sound. The quadratic resource first proves `sum kappa_i<infinity` and fixes `K=C+sum kappa_i`. Fixed-arity logarithmic sums converge by the survival estimate, so the identity

    -log D_n-K lambda_(n-1)=C(n-1)+sum_i A_n(B_i)

is valid before passing to large arity. Nonnegativity and Fatou then give `C+sum ell_i<=L_T`, establishing summability of `ell_i` without assuming the desired equality.

For a strict cell, changing the binomial reference coin to `alpha=b/(a+b)` is an exact finite-sum identity. Jensen and `a alpha^2+b(1-alpha)^2=kappa` yield

    -log d_n <= kappa lambda_n+n D(alpha||g),
    0 <= A_n/n <= kappa(1-1/n)+D(alpha||g) <= kappa+ell.

This holds for every strict parameter tuple without a common lower bound on coins or arm fractions. The boundary bounds require no passage of a potentially divergent relative entropy to an endpoint: the all-on-zero-arm or all-on-finite-arm routing term directly gives the claimed bound. Endpoint ordinary factors and the identity satisfy it explicitly. Thus the already summable sequence `kappa_i+ell_i` dominates all `A_n(B_i)/n`, and dominated convergence proves

    C+sum_i ell_i=L_T.

The Pinsker consequence, the two target-asymptotic conventions, and `beta_i=kappa_i-ell_i` are consistent. In particular `sum |beta_i|<infinity`, `sum beta_i=beta_T`, and the exact residual identity (17) follow without a rearrangement of conditionally convergent terms. No sign or logarithmic-scale domination of those residuals has been established or used.

## 4. Source contract, reuse and limit of acceptance

The same closed cells and tuple are used at every arity. The inherited ordered compactification selects ranked physical cell records and their chronological positions independently of the cap; its capwise truncation estimates may then be applied to that one selection. This does not authorize independently chosen finite-cap carriers. The ordinary complement is measured in the inherited pair-hazard clock, not an assumed bound on total arm exposure.

I inspected the relevant inherited contracts: the three-lineage survival provider (`b76a73adcbc1f52f855ff633571452f4f1a992f1e0e28b3dc59a26e82b6b083c`), ordered closure provider (`fe478d5bd68471a39e6cfa39d91a1e152d3196e0f2f9e6e895ab3906fee66eb8`), and earlier finite-unequal/countable-equal normalization (`1f6f5edd6904d999d30d73581908f3f6e18b245871fc0c4c7a9fae6cc304deb5`). Their reconstruction is not claimed as new work here.

The new accepted implications are the arbitrary-unequal quadratic survival domination and the nonnegative shifted-remainder/Jensen argument giving exact linear normalization. The hypotheses concern a compatible analysis carrier and exact all-arity diagonal matching. They do not admit boundary or infinite sources as rivals, replace the legal observation menu with latent diagonals, prove finite persistence, determine chronology, or produce either master alternative for finite INDEPENDENT observations.
