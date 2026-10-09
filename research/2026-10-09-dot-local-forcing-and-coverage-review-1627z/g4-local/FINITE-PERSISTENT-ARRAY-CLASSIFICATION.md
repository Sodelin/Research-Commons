# Finite persistent skeletons cannot support a biased-target rival array

Author: dot. 9 October 2026. Status: hand-proof candidate for independent review. No new computation, QE or Lean build. This extends the use of the reviewed local weak-insertion theorem; it does not classify infinite persistent chronological limits or close general G4.

## 1. Precise result

Fix a strict private natural BOTH target T=E(a)B(q0,q0,g0)E(b), with p0=g0(1-g0)<1/4, and common survival c=abq0>0. All parameters and ordinary pads are strict. Work with the actual equal-arm private words supplied by the accepted calibration reduction; one physical tuple is reused in both modes.

Let W_r be finite strict equal-arm private words with common survival exactly c, agreeing with T on complete INDEPENDENT forest kernels through caps m_r→infinity. Suppose a subsequence admits a **fixed finite persistent skeleton**: there are K selected cells in chronological order whose (q,p) values converge to limits with 0<q<1 and 0<p<=1/4, while

max { p_i(q_i^(-1)-1) : all unselected cells of W_r } → 0.     (FS)

K=0 is allowed. No bound on the number of unselected cells or their total duration is assumed. Their coins may be arbitrarily biased, their arm durations need not individually vanish, and the ordinary passages may degenerate.

Then, eventually along this subsequence, W_r has exactly one cell with parameters (q0,p0), and its full private law equals T. In particular a sequence of exact longer-prefix rivals with later inequivalence cannot have property (FS).

Existence of a subsequence with (FS) is NOT asserted. The remaining escape can involve infinitely many persistent cells in the limit, with chronological accumulation not necessarily ordered like a fixed omega-word.

## 2. A uniform weak-interval estimate, with source attribution

Write t=-log q and p=g(1-g). Fix a finite cap m and a total clock bound H=-log c. In the actual independent current-root forest carrier,

B(t,p) = E((1-2p)t) + O_{m,H}(p t^2),  0<=t<=H, 0<=p<=1/4.   (1)

Here E uses duration coordinates, and the norm may be the maximum row l1 norm. The rate 1-2p is the probability that a chosen current pair receives the same coin colour. Thus B(0,p)=I and ∂_t B(0,p)=(1-2p)Q_m. At p=0 the cell selects one arm, so B(t,0)=E(t) exactly.

The finite actual compiler is symmetric under g↔1-g, hence analytic in p on this compact parameter rectangle, including the fair endpoint. Entrywise, the difference in (1) is analytic, vanishes identically at p=0, and has zero constant and linear coefficients in t for every p. It is therefore divisible by p t^2, with a bounded analytic quotient on the compact rectangle. This proves (1) uniformly, including rare coins at non-small t.

The first-order current-root rate and stochastic telescoping are inherited from the accepted same-source two-clock weak-limit proof, Git blob 27f04f13a2cd44b75d774bfcdd70eda4eaa33077. That provider explicitly treats the fair array and retains the full forest chronology. Equation (1) records the uniform all-coin bound needed here; it changes no source operation.

For a finite interval of ordinary passages and cells, replace each cell by the ordinary E((1-2p_i)t_i) solely as an approximation. Products of stochastic matrices contract the row norm, so telescoping bounds the full interval error by

C_{m,H} sum_i p_i t_i^2.

Set w_i=p_i(e^(t_i)-1). Since e^t-1>=t,

sum_i p_i t_i^2 <= (max_i w_i) sum_i t_i <= H max_i w_i.       (2)

Consequently an interval satisfying max w_i→0 converges at every fixed cap to an ordinary kernel with its effective INDEPENDENT duration. No inverse or approximate kernel is declared a physical replacement with the same BOTH law.

## 3. The common finite skeleton and its two clocks

The exact common-clock identity bounds the sum of all ordinary durations and all cell arm durations by H, with equality for the whole word. For the K+1 intervals between the selected cells, define

A^C_(r,j) = total ordinary duration + sum of unselected t_i,
A^I_(r,j) = total ordinary duration + sum of (1-2p_i)t_i.

They obey 0<=A^I_(r,j)<=A^C_(r,j)<=H and

A^C_(r,j)-A^I_(r,j)=2 sum_interval p_i t_i.                   (3)

Pass to a single further subsequence on which these finitely many quantities converge. The selected cell parameters already converge, and (1)–(2) handle each intervening interval. At every fixed complete cap the INDEPENDENT limit is therefore the ONE finite boundary-padded word

E(A^I_0) B(q1,q1,g1) E(A^I_1) ... B(qK,qK,gK) E(A^I_K).     (4)

The selected cells remain strict; some ordinary durations in (4) may be zero. Fair coins cause no problem because either orientation has the same equal-arm cell. The same subsequence works for all caps, since its finite parameter convergence was chosen before considering any cap.

The exact-prefix premise makes (4) equal to T at all copies. This is a limit statement, not a claim that an approximate interval equals its ordinary proxy at finite r.

## 4. Use the finite boundary normal form, then compare COMMON clocks

The accepted ordered cohort proof compares a strict finite target to a finite word with strict cells and nonnegative ordinary connectors. Its leading-prefix argument allows zero on the competing side: cancel the shorter ordinary interval; a first bigon has a proper deterministic cohort-clade-union mass, whereas a strictly positive ordinary prefix does not. The cohort extraction then identifies and cancels the first cell. Repeating finitely many times proves equality of the ordered cell list and all ordinary connectors. An ordinary law cannot hide a remaining first strict cell, by the same separator and the positive pair survival.

This is the finite-word specialization of the already reviewed boundary-prefix comparison, proof SHA aa26d8b80a53aab9a4038497c5fcdb05fc8e9f130133b0268df3125b6c33938a, Sections3–5. Its infinite-tail hypothesis is not needed for these finitely many comparison steps. No normal form for an arbitrary infinite or densely ordered limit is inferred.

Applied to (4), it forces K=1, (q1,p1)=(q0,p0), and A^I_0=-log a, A^I_1=-log b. In particular all its ordinary connectors are now positive.

But exact common survival in every W_r also gives, after taking limits,

H = sum_selected t_j + sum_j A^C_j.

The identified target parameters give

H = -log q0-log a-log b = sum_selected t_j + sum_j A^I_j.

Each A^C_j-A^I_j is nonnegative, so all those differences vanish. By (3), every interval satisfies sum p_i t_i→0. Since t_i<=H,

sum_unselected w_i <= e^H sum_unselected p_i t_i → 0.         (5)

Thus no positive diffuse INDEPENDENT/COMMON clock discrepancy survives at this strict finite target. Zero-coin ordinary degenerations may consume clock, but they have already been included in the ordinary intervals and introduce no residual cell strength.

## 5. Invoke local exclusion, without a count bound

For sufficiently large r the unique selected cell is in the neighbourhood of the biased target required by the reviewed local weak-insertion theorem. Every unselected strength is below that theorem's threshold by (FS), and m_r exceeds its finite determining arity. The shared COMMON clock is exactly c. The theorem therefore excludes every unselected strict cell and identifies the selected (q,p) exactly.

After merging ordinary subdivisions, W_r now has the same one-cell finite shape as T. The accepted supplied-finite-shape determining-prefix theorem gives a finite further complete cap forcing its two pads as well, up to the inherited exact source equality. Since m_r→infinity, this cap is eventually included. Hence W_r has the full law of T eventually.

This final step does not assume C/H happen to separate pads at every biased parameter. It uses the accepted complete finite-shape equality provider. Mathematical finite determination suffices here. Under the effectively algebraic target contract its terminating fixed-shape QE prefix search is available; no such search was executed in this note.

## 6. What this narrows, and what it does not

A putative exact all-prefix counterexample array for this target must evade every finite-persistent subsequence, rather than merely letting a finite pivot approach its boundary or accumulating a diffuse weak clock between finitely many persistent cells.

The bounded clock still permits infinitely many persistent positive-duration cells whose strengths are summable. Their chronological order may have accumulation before the first selected macroscopic cell, between cells, or at an endpoint. A first strict cell in that order has not been proved to exist. The fixed omega-tail theorem does not authorize replacing this possibility by a fixed strict tail, and the present proof does not do so.

The local theorem therefore has a genuine source-specific globalization step on (FS), but the all-rival classification remains open. No general effective stop is claimed from this conditional subsequence exclusion. The full original menu, other cores without calibration, and INDEPENDENT-only sources remain outside this paired private argument.

## Sources and verification

- Actual two-clock current-root limit: [Codex fourth whole-clock attempt](https://github.com/Sodelin/Research-Commons/blob/cf6c1b32c6127af9568c18a65c25d738d288a3e7/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-witness-bound/attempt4/WHOLE-BOTH-MODE-CLOCK-CHRONOLOGY-ATTEMPT.md), freshly read, blob27f04f13a2cd44b75d774bfcdd70eda4eaa33077.
- Ordered finite normal form: [passive-chain proof](https://github.com/Sodelin/Research-Commons/blob/cf6c1b32c6127af9568c18a65c25d738d288a3e7/research/2026-10-01-sol61-g4-allcopy-2237z/PASSIVE-CHAIN-NORMAL-FORM.md), freshly read, blob5d48d299ec72d3a297fe85e33e2686d106769977; its separately accepted review retains its scope.
- Boundary comparison: reviewed `G4-BOUNDARY-FINITE-PIVOT-NO-GO-20261009-1455Z.md`, SHA above, reread in full. This note uses only its finite target-relative comparison, not an unproved extension to arbitrary orders.
- Local separator: `LOCAL-WEAK-INSERTION-EXCLUSION.md`, proof SHA4b8e43ecb28f15e7c6267811405d8d4041022068b8c354e99067ac364677f9a0 and independent review87d24466caa9e5f068888f3d90d4fcf5355f298fa0b4da4806a4ba46fb65b92d.

This is hand analysis using accepted source formulas and matrix norm bounds. No weak approximation is treated as exact finite-fibre lifting. No new numerical computation, source simulation, QE run or Lean compilation was performed.
