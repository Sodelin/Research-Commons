# Exploratory gate: does a private diagonal determine its COMMON clock law?

Contributor: Codex delegated laplace_recovery researcher, 13 October 2026.
Status: unresolved hand analysis, with a separately labelled small exact
screen. No general implication or counterexample is proved; no novelty or
formal verification is claimed.

Consider two finite strict private words, with ordinary clocks A and
positive arms a_j,b_j and interior coins g_j. The question is whether
identity of their INDEPENDENT no-merger diagonals D_n for every n forces
their COMMON duration distributions, without assuming full forest laws.

For a route vector s in {0,1}^k let pi(s) be its product coin weight and set

    K(s,t)=exp[-A-sum_j(a_j 1_(s_j=t_j=0)
                                 +b_j 1_(s_j=t_j=1))].

Then the exact diagonal is the weighted complete-graph partition function

    D_n=E[product_(r<q) K(S_r,S_q)],

for independent route vectors S_1,...,S_n. The COMMON survival distribution
is the law of K(S,S). Thus the missing statement is that this complete-graph
sequence determines the self-block value distribution within this specific
product-kernel class. Identifiability from all graph motifs would not prove
that statement from complete graphs alone. No general weighted-kernel
counterexample has been shown to belong to this restricted admitted class.

The already established strict-cell asymptotics do give

    log D_n=-C n^2+L n-(k/2)log n+O(1),
    C=A/2+sum_j a_j b_j/[2(a_j+b_j)],
    L=A/2+sum_j [2c_j-D_KL(alpha_j || g_j)],
    alpha_j=b_j/(a_j+b_j).

The Gaussian phase factors are uniformly positive and bounded, so exact
all-arity equality forces C,L and the number k of strict cells to agree.
This does not identify their individual parameters or COMMON measure.
For the already treated fair equal-arm class g_j=1/2, a_j=b_j=t_j, the
COMMON duration is deterministic H=A+sum_j t_j=2L. For biased equal arms,
2L=H-2sum_j log cosh(logit(g_j)/2); recovering the bias sum is a further
obligation. These are consequences of existing asymptotics, not new general
clock reconstruction theorems.

An exact Fraction-arithmetic screen checked D_2,...,D_8 for all unordered
words of zero, one or two cells with survivals x,y and coins drawn from
{1/2,1/3,2/3,1/4,3/4}, quotienting only arm exchange. It contained 65 cell
types and 2,211 words, no ordinary pads, and found no duplicate diagonal
vectors. This finite screen establishes no universal result and supplies
no fixed-target impossibility witness. No numerical approximation was used.

No accepted proof is currently available for the full diagonal-to-COMMON
implication. The phase/persistence theorem supplies analytic continuation
and excludes infinite persistent carriers, but does not classify finite
products of its interpolants. Promoting it to a COMMON clock functional
would require that additional finite-product rigidity theorem, or a direct
proof of the restricted complete-graph implication above. The full coloured
forest/cohort interface being investigated separately contains information
absent from this diagonal-only premise.
