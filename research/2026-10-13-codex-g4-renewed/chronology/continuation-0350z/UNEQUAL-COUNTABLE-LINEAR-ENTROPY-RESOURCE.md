# Exact linear normalization for general unequal countable carriers

Contributors: Codex lead G4 researcher (shifted-exposure bound and Fatou proposal); Codex / laplace_recovery (independent derivation, boundary classification, change-of-measure Jensen domination and written proof), 14 October 2026.

Status: HAND proof; independent review pending. This is an exact scalar resource identity for an actual-source compactification, not finite persistence or a finite INDEPENDENT certificate. Closed boundary factors are auxiliary limit objects, not admitted infinite or boundary rivals. No historical novelty or formal verification is claimed. This amended version strengthens its initial Fatou inequality to equality using a summable Jensen bound.

## 1. Exact premise and conclusion

Use one compatible chronological private-word carrier from the completed pair-hazard compactification, with ordinary complement C>=0 and finite or countably many closed cells B_i. Its no-merger coordinates are

    D_n=exp(-C lambda_n) product_i d_n(B_i),
    lambda_n=n(n-1)/2,       D_3>0.                         (1)

All coordinates use the same cells and parameter tuple. Suppose these coordinates equal those of one fixed finite strict private target T for every n. Equality of complete private endpoint laws is sufficient but is not needed beyond these diagonals.

For a strict cell with positive finite arms a,b and interior coin g, put

    alpha=b/(a+b),    kappa=ab/(a+b),
    D(alpha||g)=alpha log(alpha/g)
                 +(1-alpha)log((1-alpha)/(1-g)),
    ell=kappa/2+D(alpha||g).                               (2)

The ordinary quadratic rate is normalized by lambda_n: the rate kappa here equals twice gamma in the companion quadratic note. Extend kappa and ell to every closed cell with d_3>0 by the table in section 3. Define the fixed finite target budget

    L_T=C_T+sum_(target cells)[kappa/2+D(alpha||g)].          (3)

Then

    C+sum_i ell_i = L_T < infinity.                        (4)

In particular,

    sum_(strict retained cells) D(alpha_i||g_i) < infinity,
    sum_(strict retained cells) (alpha_i-g_i)^2 <= L_T/2.   (5)

No lower bound on either arm fraction or routing coin, no rational balance, no COMMON observations, and no upper bound on total physical exposure or number of cells is assumed. The proof first obtains finiteness by Fatou, then uses a new summable domination bound to prove equality. No linear resource is lost in the countable tail under the stated exact target-matching premise.

## 2. A nonnegative shifted quadratic remainder

For a strict cell and integers j,l>=0 with j+l=n, the routing exposure satisfies

    a lambda_j+b lambda_l >= kappa lambda_(n-1).           (6)

For j,l>=1, set r=j-1 and s=l-1. Cauchy--Schwarz and kappa<=min(a,b) give

    a r^2+b s^2 >= kappa(r+s)^2,
    a r+b s >= kappa(r+s).

Add and divide by two. Since r+s=n-2, this is (6). If one of j,l is zero, (6) follows directly from a,b>=kappa. The same inequality holds for every closed nonsingular case in section 3, either directly on routing terms with nonzero probability, or by setting the right-hand side to zero when kappa=0.

The cell formula is a convex average of exp(-a lambda_j-b lambda_l). Hence

    d_n(B) <= exp[-kappa(B) lambda_(n-1)],
    A_n(B):=-log d_n(B)-kappa(B) lambda_(n-1) >=0.         (7)

This is an exact inequality at each integer n, not a saddle approximation. In particular it remains valid at very small arm duration and at rare-coin boundary limits.

## 3. Every nonsingular closed-cell linear limit

For each individual closed cell with d_3>0, the limit

    lim_(n->infinity) A_n(B)/n = ell(B)                    (8)

exists. The complete list, with symmetric arm exchanges understood, is:

| Cell | kappa | ell |
| --- | --- | --- |
| Interior coin, finite positive arms a,b | ab/(a+b) | kappa/2+D(b/(a+b)||g) |
| Interior coin, one arm zero and the other positive, possibly infinite | 0 | -log pi, where pi is the routing weight of the zero arm |
| Interior coin, one arm infinite and the other finite positive b | b | -log pi, where pi is the routing weight of the finite arm |
| Both arms zero | 0 | 0 |
| Endpoint coin, used arm of finite duration t | t | t |

Unused endpoint-coin arms have no effect. An infinite used arm at an endpoint coin, or two infinite arms at an interior coin, would give d_3=0 and is excluded. These cases exhaust the closed parameter cube with d_3>0.

For strict finite arms, reuse the established uniform-in-integer-n saddle asymptotic

    log d_n=-kappa n^2/2+(kappa-D(alpha||g))n
                -(1/2)log n+O(1).                        (9)

The bounded O(1) term includes all lattice phases, with no rationality restriction. Subtracting kappa lambda_(n-1)=kappa(n^2-3n+2)/2 gives (8) with the first row of the table.

For one infinite arm and one positive finite arm b, only zero or one root can take the infinite arm without merger. Writing pi for the finite-arm coin,

    d_n=pi^n exp(-b lambda_n)
            +n(1-pi)pi^(n-1)exp(-b lambda_(n-1)).         (10)

After factoring the second term, its logarithmic bracket is log n+O(1); (8) gives -log pi. If b=0, the same formula gives the zero-arm row.

For a zero arm with routing weight pi and a finite positive other arm b, all roots may use the zero arm, so d_n>=pi^n. Conversely, with r roots on the positive arm,

    d_n=pi^n sum_(r=0)^n binom(n,r)
              [(1-pi)/pi]^r exp[-b r(r-1)/2].             (11)

Bound binom(n,r)<=n^r, complete the square in

    -b r^2/2+[log n+log((1-pi)/pi)+b/2]r,

and sum the resulting Gaussian lattice majorant. Its sum is bounded uniformly in its center by a constant depending only on this fixed b. Thus

    log d_n=n log pi+O((log n)^2).

Since kappa=0, this proves the second row. Endpoint-coin and both-zero rows are immediate from ordinary or identity evolution. No estimate in this paragraph is being summed over different cells.

## 4. Fatou supplies finiteness; Jensen supplies exact equality

The companion [quadratic survival and resource theorem](UNEQUAL-ALL-ARITY-QUADRATIC-SURVIVAL-RESOURCE.md), frozen SHA256 `ed479df354f73c1476d28d5b0791f881c790cbe43d5b02a6d2a570b59b6f8d2e`, proves

    sum_i kappa_i<infinity,
    K:=C+sum_i kappa_i=C_T+sum_(target cells) kappa_i.      (12)

It uses the actual source estimate d_n>=d_3^[65 lambda_n] to justify the quadratic dominated-convergence step even for arbitrary unequal countable cells. That step is a supplier here; it is not assumed from formal termwise asymptotics.

At fixed n, all logarithmic sums in (1) are finite by the same survival bound. Since sum_i kappa_i is also finite, subtracting the two convergent nonnegative sums yields the exact identity

    -log D_n-K lambda_(n-1)
       =C(n-1)+sum_i A_n(B_i).                            (13)

For the finite target, (8), ordinary evolution, and equality in (12) show that the left side of (13), divided by n, tends to L_T. Every summand on the right is nonnegative. Fatou therefore gives

    C+sum_i ell_i <= L_T.

This proves finiteness of sum_i ell_i before any attempted linear dominated-convergence interchange. To upgrade the inequality to equality, use the following bound for every single closed nonsingular cell and every n>=2:

    0 <= A_n(B)/n <= kappa(B)+ell(B).                       (14)

For a strict cell, change the binomial reference measure from g to the arm balance alpha. The exact finite sum becomes

    d_n(g)=E_(K~Bin(n,alpha)) exp[
        -a lambda_K-b lambda_(n-K)
        +K log(g/alpha)+(n-K)log((1-g)/(1-alpha))].         (15)

Jensen's inequality, together with

    a alpha^2+b(1-alpha)^2=kappa,

gives

    -log d_n <= kappa lambda_n+n D(alpha||g).

Therefore

    A_n/n <= kappa(1-1/n)+D(alpha||g)
           <= kappa+ell.                                 (16)

This is uniform in n. Each use of Jensen concerns one fixed finite cell, so extreme parameters require no uniform interiority assumption. For a zero-arm cell, the all-on-zero-arm route gives d_n>=pi^n, hence A_n/n<=ell. For one infinite arm and one finite positive arm kappa, the all-on-finite-arm route gives d_n>=pi^n exp(-kappa lambda_n), hence A_n/n<=kappa+ell. Ordinary endpoint-coin factors have A_n=kappa(n-1) and ell=kappa; the both-zero factor has A_n=0. Thus (14) covers the full table.

Both sum_i kappa_i and sum_i ell_i are now known finite. Dominated convergence in (13), using (14), gives (4) with exact equality. On the strict subfamily ell_i>=D(alpha_i||g_i), yielding its summability in (5). The elementary binary Pinsker inequality D(alpha||g)>=2(alpha-g)^2 follows by differentiating twice in alpha: D''=1/[alpha(1-alpha)]>=4, while D(g||g)=D'(g||g)=0. It yields the second part of (5).

If a different convention writes the target asymptotic as

    log D_n(T)=-K lambda_n+beta_T n+O(log n),

then L_T=K-beta_T. Under n-squared normalization

    log D_n(T)=-K n^2/2+B_T n+O(log n),

the same number is L_T=3K/2-B_T. These are identical conventions, not different budgets.

For a precise subsequent logarithmic analysis, define beta_i=kappa_i-ell_i. Then sum_i |beta_i|<infinity and the two proved resource identities give

    sum_i beta_i=beta_T.

Consequently the normalized remainders

    r_i(n)=-log d_n(B_i)-kappa_i lambda_n+beta_i n

have an absolutely convergent sum at each fixed n, and

    sum_i r_i(n)
       =-log D_n(T)-K lambda_n+beta_T n.                  (17)

Absolute convergence follows from the already finite sums of -log d_n, kappa_i and |beta_i|. Equation (17) is exact; no sign or logarithmic-scale uniform bound on its summands is claimed.

## 5. Attribution, applicability and remaining gap

The [earlier finite-unequal/countable-equal resource proof](../continuation-2110z/UNEQUAL-RESOURCE-NORMALIZATION.md), SHA256 `1f6f5edd6904d999d30d73581908f3f6e18b245871fc0c4c7a9fae6cc304deb5`, already proves the strict single-cell asymptotic (9) for all real arm balances and the linear equality in its equal-tail setting. Its proof of (9), and the accepted pair-hazard compactification cited in the companion, are reused. The new ingredients here are the globally nonnegative shifted remainder (7) and its change-of-measure domination (14), giving the exact linear entropy resource for *arbitrary unequal* countable closed carriers. The earlier marked-history entropy-cost route concerns a different observable/history divergence and is not being claimed as reconstructed.

The result discharges general exact linear-resource normalization after exact quadratic normalization. It does not control the logarithmic residual uniformly over the countable family, remove endpoint factors, or classify all-order unequal saddle phases. In particular, (5) does not imply summability of coin logits or of inverse-arm-weighted squared bias; arm balances and coins may both approach a boundary. Equation (17) cannot be combined with Fatou at logarithmic scale without a new sign or domination argument. No finite carrier or source-size bound follows.

The fixed-target all-arity diagonal premise is still an analytic limiting premise, not a finite legal-observation certificate. No all-prefix inequivalent admitted rival is constructed. The general finite INDEPENDENT master and the weak-reservoir chronology obstruction remain open.

Verification: explicit hand inequalities, single-cell asymptotics supplied by the pinned earlier proof, Fatou's lemma and dominated convergence. No new computational test, source compiler, Lean or Rust verification is asserted.
