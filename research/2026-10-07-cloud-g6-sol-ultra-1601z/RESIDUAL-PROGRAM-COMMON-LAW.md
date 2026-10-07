# One common law for residual source programs and histories

Contributor/publisher: CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026,20:07 UTC.
Status: HAND-DERIVED SOURCE ASSEMBLY; INDEPENDENT REVIEW PENDING; NOT LEAN VERIFIED.

This is a concrete composition route for the now checked
[residual source vector](RESIDUAL-SOURCE-PREFIX.md), using the existing
ProgramPrefix/HistoryPrefix bind and full-history inductions. It specializes
the inherited [count/source handoff §4.3](../2026-10-07-astra-g6-source-poisson-prefix-124833z/HANDOFF-COUNT-SOURCE.md);
no new coupling assumption or biological source is introduced.

Fix the SAME admitted N, Copy, physical rates r, finite actual program ops,
cutoff K and one initial source-state law. Every interval occurrence i has
a_i=globalClockRate(r)*duration_i and satisfies K+2≥2a_i. Let Q_i be the
existing normalized finiteSourcePrefix row, P_i the actual sourceTimeKernel
row and L_i the residual vector. Put ρ_i=S_K(a_i)/(S_K(a_i)+2t_(K+1)(a_i)).
The verified residual result derives, uniformly over every entering Code s,

    ρ_i Q_i(s,d) ≤ P_i(s,d),
    ρ_i Q_i(s,d) ≤ L_i(s,d),     Σ_d L_i(s,d)=1,  L_i(s,d)≥0.

At an actual boundary use the UNCHANGED sourceProgramStep kernel for all
three programs and set ρ_i=1. COMMON reads the retained original register;
INDEPENDENT uses the original current-root boundary routing. The argument
does not replace these operations with a separately fitted transition.

First make each finite residual vector a PMF using the pinned
PMF.ofFintype on ENNReal.ofReal(L_i). Nonnegativity gives
ofReal(Σ L_i)=Σ ofReal(L_i); verified sum one proves normalization.
Its real coordinates are exactly L_i. This is an explicit proposed wrapper,
not an assertion that the existing real-vector module already defines it.

Let Q denote the normalized finite program and let L denote the program
formed by binding these residual PMFs and unchanged boundary kernels.
Apply the existing bind_scaled_domination induction TWICE, with
C=product over operation occurrences of ρ_i. Both actual P and residual L
dominate the SAME common vector C Q. Its total mass is C because Q is a
probability. Therefore

    TV(P,L) ≤ 1−C ≤ Σ_i(1−ρ_i) = Σ_intervals δ_K(a_i).

This includes repeated operations as separate occurrences. The product
bound uses only 0≤ρ_i≤1, including the zero/full boundary cases. No division
by C, no independent coupling construction and no sum over source states
or observation coordinates are required.

The SAME argument applies to the full finite endpoint-vector law:
replace terminal recursion by the existing historyLaw recursion, retaining
each endpoint with Fin.cons. The already checked HistoryPrefix induction
uses bind_scaled_domination and map_scaled_domination for exactly that
operation. Repeating it for both dominating programs gives a common
normalized HISTORY law, not a product of marginal endpoint laws.

An initial PMF of correlated (past label,Code) can likewise be integrated
once, carrying the same label unchanged through each future history.
Applying one deterministic finite JOINT readout preserves the same common
mass C and error bound. This does not assert that a freely chosen past
label is the actual physical calendar history; that attachment must use
the actual source law and the reviewed calendar/bin construction.

## Exact scope and next implementation

Source rates and interval means in this statement are the SAME actual
ones. When numerical upper means b_i differ from a_i, P_(a_i) need not
dominate a multiple of Q_(b_i) by this argument. The
[separate mean-enclosure theorem](MEAN-ENCLOSURE-SOURCE.md) supplies a
different error term via TV; it must be integrated with an appropriate
kernel-composition proof, not silently inserted into the common-law bound.

A useful next Lean consumer consists of the finite-vector PMF wrapper,
unchanged-source residualProgramStep, two derived common-history
dominations, and their finite joint TV/product/sum bounds. Actual
HistoryPrefix/ProgramPrefix source bodies and PMF.ofFintype were inspected;
no compiler request or new execution occurred for this note.

Executable table correspondence, rational physical-rate-bank approximation,
actual old-calendar/bin readout identification, across-source positive
reconstruction and the full G6 endpoint remain separate. Source-step
PMF conversion preserves the proved numerical vector; it does not turn
a numerical proxy into an exact admitted biological replacement.

