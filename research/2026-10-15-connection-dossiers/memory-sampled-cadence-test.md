# Target-B memory: one explicit sampled-history determinant

15 October 2026. Hand/source analysis by dot. No simulation, compiler, state enumeration or new proof of nonzero determinant. This is a concrete unresolved source-defined identity, with positive-probability conditioning events proved. It advances the previous generic history question to one fully specified test at the actual readout cadence.

## Result upfront

For the fixed uniform balanced initializer and the recorded 12³ fine scan, two explicit histories with identical last five recorded blocks have positive probability. A single scalar determinant below is zero exactly when those histories give the same probability for one specified next-block scientific event. Proving it nonzero would refute a five-block-suffix predictor at that phase; it would not prove infinite memory order. Its value/sign remains unresolved. No provably closed small augmentation was found.

## 1. Exact source binding

All external files are pinned to compensated-magnet-ledger commit **45551de5fac4e69de3e03c420b31abb335d73ef4**:

- [mc_ce.py](https://github.com/spicylemonade/compensated-magnet-ledger/blob/45551de5fac4e69de3e03c420b31abb335d73ef4/materials/YBaMnFeO5/cation_order_cluster_expansion/mc_ce.py), `run`: 50 blocks, `per=max(1,nsweep//50)`, equilibration before each temperature, SRO at `b % 5 == 0`.
- [torder.py](https://github.com/spicylemonade/compensated-magnet-ledger/blob/45551de5fac4e69de3e03c420b31abb335d73ef4/materials/YBaMnFeO5/cation_order_cluster_expansion/torder.py), `scan` and fine loop: L=12 uses nsweep=4000, nequil=2000.
- [recorded main-fit result](https://github.com/spicylemonade/compensated-magnet-ledger/blob/45551de5fac4e69de3e03c420b31abb335d73ef4/materials/YBaMnFeO5/cation_order_cluster_expansion/torder_YBMFO_E_PM_best_bw_bayes.json): first `fine["12"]` temperature is **1215 K**, 28 temperatures; coarse selected peak is 900 K. The relevant metadata was freshly read. The file contains NaN outside these fields; no nonfinite parameter is admitted.
- [existing exact A/B witness](https://github.com/Sodelin/Research-Commons/blob/ab80109bcaf0edec8bc3eb58aea2fd369d824fa6/research/2026-10-15-codex-materials-exact-obstruction-2052z/MATERIALS-EXACT-MIXTURE-OBSTRUCTION-01.md).

We freeze the recorded temperature schedule as an externally supplied control, rather than claiming equivalence for the entire random coarse-peak selection algorithm. Each fine-size run initializes afresh. In the ideal independent-draw interpretation this fine-run uniform initializer is independent of the earlier coarse run; the literal seeded implementation is a separate program-semantics question.

Let X be the balanced configurations on 12³, N=1728, C=binomial(1728,864), and μ(x)=1/C. Let K be the ideal mixed Metropolis kernel at **T=1215 K**, with the frozen source binary64-lifted coefficients and exact positive KB. Then

q = 2000·1728 = 3,456,000 equilibration attempts,

m = 80·1728 = 138,240 attempts per measurement block,

P = K^m, and ρ = μ K^(q+m).

ρ is the law at the first recorded block b=0, not a stationary substitute. All these operators use the SAME couplings and temperature; parameters are never refitted or redrawn between observations.

## 2. Exact masks and histories

Let F(x) be the exact energy-per-formula-unit plus every retained labelled Fourier amplitude in source order. Let D(x) be D9F; equality of D implies equality of F. At a SRO block define the readout R(x)=(F(x), all nine normalized pair SROs), which is equivalent to D at this fixed geometry. At other blocks only F is observed.

Reuse x_A, x_B, z_B from the cited witness. Put d=R(x_A)=R(x_B) and y=R(z_B). Define diagonal 0/1 masks:

A(x,x)=1{R(x)=d},

B(x,x)=1{R(x)=y},

C₀(x,x)=1{F(x)=F(x_B)},

C₁(x,x)=1{F(x)=F(z_B)}.

The symbol C₀ is a mask, unrelated to the count C above. The two F values differ because the exact swap energy ΔE_B is strictly positive at the fitted coefficients. Masks are exact ideal-real comparisons, not floating-tolerance bins. No unobserved SRO is inserted at b=1,2,3,4 or b=6.

Define two histories through b=5:

- H_d: R at b=0 is d; F at b=1,2,3,4 is F(x_B); R at b=5 is d.
- H_y: R at b=0 is y; the same F observations at b=1,2,3,4; the same R=d at b=5.

Their last five recorded observations (b=1,…,5), temperatures, inter-observation attempt counts, and current schedule phase agree. Their first readout differs. They arise under the SAME μ, not different hidden-state initializers.

**Positive-probability proof.** Every hidden state has K(x,x)≥r=1/(2N)>0. Starting from x_B, all self-loops through b=5 give H_d positive probability. Starting from z_B, self-loops until b=0 give the first y readout; during the next block perform the reverse of the named exchange once and self-loop for all other attempts. It reaches x_B and then remains there for the remaining readouts. The arbitrary proposal supports this reverse exchange and its Metropolis acceptance is positive (indeed downhill for the fitted ΔE_B). Since μ(z_B)>0, H_y also has positive probability. Equilibration does not invalidate either path: it can consist entirely of self-loops. This proves only support, not useful event frequency.

## 3. The decisive explicit identity

Use row-vector convention and let 1 denote the all-ones column. Define

W = (P C₀)^4 P A,

a = ρ A W,

b = ρ B W,

v = P C₁ 1.

Thus a1=P(H_d)>0 and b1=P(H_y)>0. Let E be the next recorded b=6 event F(X)=F(z_B). Its conditional probabilities are av/(a1) and bv/(b1). Therefore the single exact scalar

**Δ₅ = (av)(b1) − (bv)(a1)**

is nonzero if and only if these two positive-probability histories violate five-block-suffix sufficiency for this next readout. Equivalently the 2×2 matrix with rows (a1,av) and (b1,bv) has rank two. This is a literal finite expression in the fixed source K, source-defined masks and the uniform initial law. There is no free model, invented local proposal, extra observation or unspecified temperature.

**What has and has not been proved:** the expression and equivalence are derived; both denominators are strictly positive; Δ₅≠0 has NOT been proved. Δ₅=0 would merely say this chosen pair/event fails to distinguish, not establish fifth-order Markov behavior. A nonzero result refutes every suffix length ≤5 for a predictor that receives only those suffixes and the common phase/controls. It does not refute a retained latent state or longer suffix. The same construction can be written for later h within the 50-block run with the actual time-dependent masks, but no all-h conclusion follows from one determinant.

## 4. Why the previous argument does not evaluate this determinant

At every attempted-step observation, x_A cannot leave its descriptor fibre without being detected, which proved the earlier universal-initializer corollary. Here P integrates 138,240 attempts. Paths can leave and re-enter a mask between observations; neither a nor b is a point mass. Positive contributions from one selected path give no sign for a difference of two conditional probabilities. The huge equilibration exponent does not make μK^q exactly Gibbs without a proof. Observing the same descriptor after a block does not certify that no exchanges occurred within the block.

Reversibility alone does not justify replacing the nonstationary ρ by a stationary law or turn this particular cross determinant into a nonnegative variance. Likewise K's one-step non-lumpability does not imply P's non-lumpability without an additional spectral argument; even that would not automatically establish this fixed-prior history result. These are the exact missing steps, not computation already completed.

## 5. A bounded next mathematical attack

The next task is **prove or disprove Δ₅≠0 at the specified coefficients and 1215 K**, using a source-faithful operator argument or certified bounds. A useful certificate must bound the whole determinant, including every unobserved excursion, not just the named four-state paths. Symmetry-orbit reduction or an invariant test-function span may shrink the proof, but any proposed compression must itself be certified under K and the masks. No unbounded enumeration is authorized by this note.

If the scalar vanishes, the outcome is a failed candidate witness, not a positive memory theorem. A genuinely positive small augmentation would require a closed finite-dimensional predictive subspace for these operators with the admitted initial row and actual readout masks, together with recursive update and all required future readout predictions. Full-state and full-belief existence are already known and are not counted as progress.

The masks operate on the underlying chronological scientific readouts selected for target B. The script's final means, heat-capacity estimate, Binder ratios, thresholds, tie order and undefined conventions are deterministic functions of the full block sequence. The fixed joint-record target is therefore respected, but a discrepancy for underlying block histories is not automatically a discrepancy for a separately weakened target containing only final aggregate records. No claim about synthesis kinetics, measurement noise, physical validation, infinite-volume behavior, Lean verification or mathematical novelty is made.


# Target-B determinant: energy separation and SRO-source check

15 October 2026, 23:48 UTC. Narrow source/arithmetic review. **Both required premises check; no mathematical correction to the masks in TARGET-B-MEMORY-IDENTITY-02 is required.** The determinant's nonzero value remains unresolved.

## Exact positive energy difference

Primary fit: [torder_YBMFO_E_PM_best_bw_bayes.json at 45551de5fac4e69de3e03c420b31abb335d73ef4](https://github.com/spicylemonade/compensated-magnet-ledger/blob/45551de5fac4e69de3e03c420b31abb335d73ef4/materials/YBaMnFeO5/cation_order_cluster_expansion/torder_YBMFO_E_PM_best_bw_bayes.json). Relevant coefficient fields were freshly read during this task. The frozen semantics are exact rational lifts of the parsed binary64 coefficients, not exact decimal rationals:

- V_ap = 3254063363298789 / 140737488355328;
- V_ip2 = 4814043477715793 / 1125899906842624;
- V_c2 = 4160251384624691 / 2251799813685248;
- V_ip4 = 0, the missing-key default.

For the already checked B vertical exchange, the pair-sum change in source class order is (0,4,0,16,0,0,0,−8,32). Therefore

ΔE_B = 4 V_ap + 16 V_ip2 − 8 V_c2 + 32 V_ip4

= **41128429432628793 / 281474976710656 > 0**.

The instantaneous energy-per-formula-unit readout is 2E/N, N=1728. Its change is exactly

**2ΔE_B/1728 = 13709476477542931 / 81064793292668928 > 0**.

Thus F(z_B)≠F(x_B) independently of whether any Fourier coordinate changes. A bounded Python Fraction calculation reconfirmed the three source decimal-to-binary64 ratios and both displayed identities; it did not import or execute the materials model, simulate, search states or compile. The exact-energy input and original geometric change are also recorded in the [pinned obstruction packet](https://github.com/Sodelin/Research-Commons/blob/ab80109bcaf0edec8bc3eb58aea2fd369d824fa6/research/2026-10-15-codex-materials-exact-obstruction-2052z/MATERIALS-EXACT-MIXTURE-OBSTRUCTION-01.md).

## Source actually computes all nine SRO classes

[mc_ce.py at the same immutable source pin](https://github.com/spicylemonade/compensated-magnet-ledger/blob/45551de5fac4e69de3e03c420b31abb335d73ef4/materials/YBaMnFeO5/cation_order_cluster_expansion/mc_ce.py):

1. `CLS` explicitly lists ip1, ap, Y, ip2, apd, Yd, ip3, c2, ip4.
2. `offsets()` includes the eight ip4 offsets.
3. `build` appends every neighbor and class label. It assigns coupling through `V.get(c, 0.0)`; **it does not drop zero-coupling classes**.
4. `sro` loops over `len(CLS)` and returns each class with nonzero neighbor count. All nine have nonzero counts at 12³.
5. `run` samples those values at b=0,5,…,45, accumulating all nine. The final record suppresses keys with exactly zero accumulated sum. That record filter does not mean only eight underlying SRO values were sampled.

For class c let n_c be the fixed number of directed neighbor entries. Then SRO_c=2S_c/n_c, with n_c>0. Thus all nine SRO values recover all nine pair sums. Together with the retained Fourier amplitudes, R is equivalent to D9F at fixed geometry; energy is redundant since it factors through the pair sums. This establishes the precise equivalence used in the determinant note.

The target is the selected joint chronological underlying scientific readouts, not only the final filtered aggregate dictionary. If a separate contract retained only eight SRO classes, the R↔D9F assertion would have to be removed. The determinant construction would still be definable with that weaker R: x_A and x_B remain equal in it; y differs by energy; both positive-history paths still work. No determinant nonzero conclusion would follow merely from making this change.

## Disposition

Safe to publish IDENTITY-02 as an explicit unresolved source-faithful scalar test with this check attached. Do not promote it to a proved fixed-initializer, coarse-cadence memory obstruction. The new energy separation premise is now independently checked, while the original one-attempt obstruction did not require its sign.
