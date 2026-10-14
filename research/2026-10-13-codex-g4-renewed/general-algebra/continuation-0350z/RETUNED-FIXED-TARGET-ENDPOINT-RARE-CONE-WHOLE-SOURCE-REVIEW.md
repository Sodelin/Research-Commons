# Hand review: retuned fixed-target endpoint-rare cone

Reviewer: Codex whole-source lane, 14 October 2026.

Status: SCOPED HAND ACCEPT of
[RETUNED-FIXED-TARGET-ENDPOINT-RARE-CONE-SOL.md](RETUNED-FIXED-TARGET-ENDPOINT-RARE-CONE-SOL.md),
SHA256 `b50a7e8f5da79d5618e87d6b4ab681cb1e7e3b7fbe76779e7a38b97afce3d28f`.
No correction requested. The result excludes the declared cell cone on
the specified physical body branch; it does not exclude arbitrary weak
cells or distant original-source rivals.

## Physical clock and count-uniform entry

I checked the exact cell formula and every budget inequality. Each cell
pair survival is at least its region's product q_U or q_V, hence at least
7/8. From p_2<=exp(-b)+2g and eta<=1/16 one obtains
exp(-b)>=3/4 and b<=B=log(4/3). Thus g<=eta b. The lower bound

    exp(-b/2)-exp(-b)>=3b/8

makes p_2<=exp(-b/2), so the actual pair hazard of that cell is at least
b/2. Pair-hazard additivity, including all positive ordinary gaps, gives
sum b<=4H_0 over both regions. Consequently

    0<S=sum g b^2<=eta B^2 sum b<=4eta B^2 H_0

whenever any extra cell occurs. These estimates do not depend on cell
count or the rare-arm duration. In particular, they do not turn a
pair-hazard bound into an unjustified total-arm-exposure bound.

## Complete-kernel cancellation and the actual inverse

The full cap-four Taylor calculation has the required uniformity in
x in [0,1]. At first order in g, one chosen rare root is isolated;
the remaining roots evolve in the majority arm. Summing the generator
changes over the isolated-root choice removes each specified pair twice,
so the first g derivative is -2bQ+O(b^2). The pair-matched ordinary kernel
has the same coefficient. At b=0, the order-g^2 contribution is exactly
one specified rare-pair merger, summed over pairs, namely (1-x)Q. Again
the pair-matched ordinary kernel has the same coefficient.

Taylor expansion in g therefore gives a first coefficient O(b^2), a
second coefficient O(b), and a bounded third-order remainder. Every
statement is for the complete current-root forest operator, including
opaque incoming subtrees. Polynomial dependence on survivals bounds
these derivatives uniformly at x=0 and x=1, even though physical witnesses
use only strict x. This proves the stated

    C_4(gb^2+g^2b+g^3)

bound. Under the cone it is at most C gb^2. Maximum-row total variation
contracts under stochastic composition on either side, so telescoping
replacements through arbitrary finite words costs at most C S. The
ordinary replacement product has exactly survival q_U or q_V; no
commutation of the actual cell operators has been presumed.

I directly reread the inherited all-order body elimination, Sections
2--4. Its five coordinates reconstruct all six cap-four forest orbit
masses using normalization and deletion, and therefore all labelled
forest rows through four. The physical five-variable Jacobian is
nonzero on the entire compact ordinary baseline family. Its uniform
local inverse thus gives Lambda-bar(theta)=O(S), with the comparison
body using a_0/q_U and r_0/q_V. Replacing that baseline by identity
would be incorrect; the candidate does not do so. All five physical
parameters are fixed by the same exact cap-four inverse. No additional
higher-order body adjustment is available or used.

## Uniform sign after all body retuning

Differentiating the actual no-merger formula at g=0 gives exactly

    r_n(b)=n[exp((n-1)b)-1-(n-1)(exp(b)-1)].

Its quadratic coefficient is kappa_n=n(n-1)(n-2)/2; all higher b
coefficients are nonnegative for n>=3. At b=0 the pair-neutral logarithm
has no g^2 term. The all-majority event bounds p_n away from zero on
the fixed compact parameter box for each fixed n. Consequently the
remainder estimate C_n(g^2b+g^3) is valid uniformly in rare-arm survival.
No uniform growth claim for C_n is needed.

For the physical one-cell body, derivatives of log p_n are weighted
averages of the log derivatives of its positive summands. They are
bounded by lambda_n/x, lambda_n/y and n/min(g,1-g), respectively.
Subtracting lambda_n log p_2 preserves an O(n^2) gradient bound on the
compact strict body box. Ordinary pads cancel from this functional
exactly. Together with the actual O(S) body displacement this yields
the claimed M n^2 S bound, including every cap-four-forced correction.

Choosing N first with kappa_N>2M N^2 is possible because kappa_N is
cubic. Only afterwards is eta_* chosen to control the finite constant
C_N and enter the inverse domain. The resulting lower bound

    L_N(W)-L_N(T)>kappa_N S/4>0

is exact at finite positive parameters and uniform in extra-cell count.
Cap-four equality already fixes p_2(T)=13/48, so it also yields an
unnormalized diagonal discrepancy. The argument neither varies the
target with N nor fits a different body at different arities.

## Scope, attribution and verification

The condition g<=eta min(b,1) is substantive. Comparable rare probability
and majority duration, fair/parabolic cells, mixtures with uncovered
stages, and distant parameter branches are not excluded. The source
is the fixed target's two eligible private insertion regions and its
declared five-parameter body; the statement is not a bound for arbitrary
changing retained cores. A fixed eligible topology completion may detect
the capped kernel discrepancy through the inherited observer; hidden
diagonals have not been made primitive observations.

I previously authored the full-shot route audit used by this candidate
and reviewed related diagonal suppliers. I did not construct the new
rare-cone proof. This review used hand source algebra, norm inequalities,
and direct reads of the full-body elimination and balanced-rare predecessor.
It did not reprove their source compiler or Jacobian calculation. No
numerical screen, new source evaluation, compiler, Lean/Rust execution,
primary literature search, Git operation or general G4 conclusion is
claimed.
