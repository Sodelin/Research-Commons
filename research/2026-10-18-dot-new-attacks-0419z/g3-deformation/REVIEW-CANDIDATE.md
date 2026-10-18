# Concrete audit of Source10's exact-fibre deformation obstruction

18 October 2026, 04:20 UTC. Contributor: dot (OpenAI), working with Nolan.
Status: exact rational control executed and local hand argument checked in this producing pass; independent review pending. This instantiates an inherited unreviewed construction, not a new conceptual obstruction, a full review of Source10, or a G3 decision theorem.

## Finding and provenance

The proposed dimension-count/implicit-function deletion route is already treated in [Source10 §§3–6](https://github.com/Sodelin/Research-Commons/blob/e7b996990b99df791271f4ea0d47472ce760a765/handoffs/2026-10-16-codex-g3-screened-source-10/JOINT-FIBRE-NONINTEGRABILITY-AND-FAILED-UNIFORM-DELETION-10.md), explicitly unreviewed/uncompiled. Its finite rational recipe had not been executed there. Here the explicit strict node p=1/100, q=1/2 and rare-append node u=1/30 succeeds. The stored exact rational normal proves the local obstruction without needing the source's small-p rank-limit argument or its unevaluated delta prescription.

For rates Lambda=(1,3,6,10,15,21,28), put H_l(p,q)=-log(1-p+p q^l). Form the seven columns

    M=[Lambda,H_p,H_q,H_pp,H_pq,H_qq,D(u)], D_l(u)=1-u^l.

Exact rational arithmetic gives det(M) nonzero. The stored rational vector c satisfies

    c.Lambda=c.H_p=c.H_q=0,
    c.H_pp=c.H_qq=1, c.H_pq=0, c.D(u)=-1.

The checker independently symbolically differentiates H and checks all five derivative formulas at the node before solving these identities. RESULT.json contains every rational coefficient of c, rather than a rounded normal.

## Decisive hand argument

The scalar smooth function g(P,Q)=c.H(P,Q) has zero gradient and identity Hessian at (p,q). Continuity supplies an open neighborhood U contained in (0,1)^2 on which its Hessian is positive definite. Taylor's theorem therefore gives a positive kappa such that

    g(P,Q)-g(p,q) >= kappa[(P-p)^2+(Q-q)^2]

on a sufficiently small convex U. For any finite N, allow every literal head (P_j,Q_j) to vary independently and define the exact normalized source map

    G_N(a,P_1,Q_1,...,P_N,Q_N)=a Lambda+sum_j H(P_j,Q_j).

At z0=(a0,p,q,...,p,q), equality G_N(z)=G_N(z0), paired with c, forces every head unchanged by the preceding nonnegative sum. The remaining vector equation forces a=a0. Thus z0 is isolated in this normalized exact fibre. The derivative columns are Lambda and N repetitions of H_p,H_q, so rank is exactly three and nullity 2N-2. In particular N=4 already gives nine free normalized variables and only seven coordinates, with no nonconstant local exact-fibre path. Large first-order nullity does not imply integrable physical motion. This is a singular point, so the regular-level-set conclusion of the implicit-function theorem is unavailable.

## Actual strict source; normalization is not an imposed tie

Set t=1-p^2=9999/10000. Use the literal natural COMMON word

    W_N=E(t) product_j [B_COMMON(t q,t,p) E(t)].

Each arm survival, connector and routing probability is strictly between zero and one. Literal cells have distinct independent natural coins; sharing a probability value at this center does not tie the random draws or restrict competing parameter variations. Its random survival is t^(2N+1)q^(sum_j Z_j), Z_j independent Bernoulli(p), giving rational moments

    m_l=t^((2N+1)l)(1-p+p q^l)^N.

The baseline is a0=-(2N+1)log(t)>0. In a neighborhood of this actual word, unequal arm ordering remains fixed. Each cell can be normalized by its larger arm survival; all deterministic arm scales and ordinary connectors enter only through the single baseline a. There are redundant physical scale/subdivision directions, but they leave normalized heads and a unchanged. They cannot move p to 0 or 1, or q to 1, to delete a genuinely unequal randomly routed factor. The result therefore asserts isolation of the normalized response fibre, not of the full redundant physical tuple. No equal-head constraints are imposed on the competing tuple.

For the original observation interface, the inherited [attained-boundary source, §2](https://github.com/Sodelin/Research-Commons/blob/8181505bd8ebb976ae4f128f088a20f93f1f8da5/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-witness-bound/attempt2/ATTAINED-BOUNDARY-COUNTEREXAMPLE.md) was directly read. It records the accepted rational triangular calibration: seven A-monophyly rows with k=2,...,8, actual B,C,D samples followed by permitted A/B restriction, plus two B calibration rows, recover these seven moments of one pendant COMMON word. Insert W_N into that same strict four-taxon pendant construction; maximum count is eleven and all rows use one tuple. Injectivity transfers the local fixed-chart isolation to those supplied observations. This pass relies on the inherited compiler and does not execute a genealogy compiler or independently reprove its all-core theorem.

## What this does and does not decide

The local path cannot reach a deletion face: a connected exact-fibre component containing an isolated point consists only of that point. Gauge-only movement does not change this. A different exact-fibre component or graph may still realize the same observations more shortly. No minimum-size claim is made, and no input-dependent computable bound is refuted.

The same normal is not a source-wide NO certificate: c.H(epsilon,u)=-epsilon+O(epsilon^2)<0 for small positive epsilon. Legal positive deterministic padding is annihilated by c.Lambda=0. Thus the locally supporting normal fails the actual rare-append condition, exactly as Source10 warns.

The route stops before any global continuation/positivity-boundary argument: its proposed local motion already fails on an admitted strict COMMON subcase. A theorem using other components, additional cells or global representative selection would require its own source-faithful proof and an effective bound total on NO inputs. It cannot be obtained from this tangent count. No general G3 recognizer, undecidability theorem, or claim for INDEPENDENT/BOTH is supplied. Full Source10 acceptance remains unclaimed.

## Execution receipt

Installed Python/SymPy only; no installation, numerical inverse, solver or Lean run. check.py exited zero. It checks exact derivative formulas, six-column rank, invertible seventh column, all seven normal pairings, and N=2 derivative rank/nullity. The arbitrary-N isolation and original-interface transfer above are hand reasoning, not computation.

- check.py SHA256 5cc46c06c79beb5553c087f0893571ea88d4532edaac44abc297d021efc5131d
- RESULT.json SHA256 3d1b95646e80a85a21676764fab2bfae985774676949b8ccdb7f3db0de60ce47
- EXECUTION.log SHA256 fe6735bdfe8b7849070eb0d69a20fdd525dccb0e688daddc98473fbe8a019e92

No publication in this pass. Historical novelty unassessed; source attribution retained.
