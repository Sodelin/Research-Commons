# Remaining mixed-tail obstruction and a precise next attack

Contributor: Codex chronology subagent, 13 October 2026. Research checkpoint after the independently reviewed small-bad-cell and early-all-bad-tail results. Hand proof, exploratory algebra and unsupported transfer steps are kept separate.

## What is now proved at this lane's scope

- The first-primitive fixed-cell asymptotic and finite-word exponential rate are in [FIRST-PRIMITIVE-LARGE-ARITY.md](FIRST-PRIMITIVE-LARGE-ARITY.md). Finite normal-form identifiability itself is inherited.
- [SMALL-BAD-CELL-UNIFORM-POSITIVITY.md](SMALL-BAD-CELL-UNIFORM-POSITIVITY.md) proves existence of one small-cell neighborhood in which every bad cell has positive first primitive at every arity. The compact moving-scale limit was independently derived and reviewed in the [review lane](../fixed-target-negative/FIRST-PRIMITIVE-REVIEW-AND-PARABOLIC-LIMIT.md).
- [EARLY-BAD-TAIL-EXCLUSION.md](EARLY-BAD-TAIL-EXCLUSION.md) rules out a positive ordinary factor for arbitrary no-first carriers that are eventually all-bad near the first boundary. It does not assume sparse cell spacing or a lower rate on strength.

These are calibrated private BOTH consequences. They do not give a general whole-source legal decoder or finite determining certificate. A countable carrier is a limit argument and is not an admitted finite rival.

## The precise remaining carrier

An endpoint-equal countable carrier with represented ordinary prefix c<a must have good cells h_i^2<2t_i accumulating at the initial boundary. Its full diagonal equations also require a superlogarithmic bad-cell negative reservoir. The latter requirement is unweighted by source position and does not prove that bad cells accumulate at that same boundary.

At any fixed arity, every bad cell sufficiently near the initial boundary now contributes a nonnegative primitive. Good cells can contribute negatively. The existing transported negative allowance is uniformly finite, but it does not compare the exponentially small positive and negative parts at increasing arity. A negative answer still requires strict finite exact-prefix rivals to one fixed finite target; no such construction is supplied.

## Exploratory Laplace-distribution interpretation

This is exact algebra for the proved parabolic limit, not an exact representation of the source endpoint sequence. Set alpha=h^2/t and substitute y^2=alpha x into the moving-scale function:

    F(x,sqrt(alpha x))
      =[alpha x-4alpha-2+(12alpha+8)/(x+2)
                               -8alpha/(x+2)^2]/64
         -exp(-x)/32.

As a distributional Laplace transform on [0,infinity), this is

    alpha delta'_0/64 -(4alpha+2)delta_0/64 -delta_1/32
       +[(12alpha+8)-8alpha u]exp(-2u)du/64.

For physical x=n t and an ordinary-looking transport exp(-n s), the derivative atom moves to s and has coefficient h^2/64. That coefficient is positive whenever the cell is biased. The finite bias budget makes sum h_i^2 finite after discarding finitely many large h_i.

This suggests a stronger route: prove an actual endpoint generating-function or distributional representation in which a cell's positive derivative atom at its own start cannot be cancelled by ordinary measure terms. A finite atomic measure cannot have a distributional derivative equal to a finite measure unless the atoms vanish. With countably many cells, local finite-variation and accumulation hypotheses would have to be proved from the actual source, rather than assumed.

There are two unsupplied transfers:

1. The displayed formula is only a moving-scale limit. The exact chronological transport is chi_n(prefix), not exp(-n s), and its subexponential correction can be important.
2. Extracting a nonzero boundary tangent requires controlling normalization. Cell strengths can decay faster than any fixed scale in their start positions; an unnormalized rescaled limit can be zero even when infinitely many cells remain. The inherited sparse example already cautions against any polynomial lower bound.

Thus the positive derivative-atom observation is a proposed analytic handle, not a proof of ordinary-prefix rigidity.

## Other approaches checked and not promoted

- Scalar maximal positive Wright-Fisher smoothing only excludes c>=a by the inherited atom/overshoot argument. At c<a the target residual is itself smoothed and atomless, so positivity alone supplies no contradiction.
- A source-sensitive regenerative decomposition of the full hierarchy could be stronger: a finite target's initial Kingman region has a finite entrance partition and conditional Kingman subhierarchies. Generic Gibbs/Markov-branching classification does not establish that a reticulate carrier has the required conditional independence or that its entrance cut is observed. Literature search surfaced Berestycki--Pitman and McCullagh--Pitman--Winkel on Gibbs partitions/fragmentation trees; only metadata/abstracts were inspected in this lane, so no theorem from them is used.
- The complete-forest spectral blocks n->r with fixed r would have quadratic attenuation under a positive ordinary prefix. The sibling spectral lane has a valid finite projector norm envelope. The missing converse is a source lower bound preventing every such block from becoming quadratically small in a no-first carrier; no claim is made from the envelope alone.

The next substantive obligation is a source-sensitive comparison of the interlaced good-cell negatives with the now uniformly positive bad-cell contributions, or an exact full-forest analytic substitute. No source count, hidden motif oracle, positive physical inverse or changed fixed target has been introduced.
