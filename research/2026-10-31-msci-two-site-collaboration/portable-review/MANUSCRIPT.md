<!-- Generated internal reading edition; see PACKAGES.json and assemble.py. -->

# Two-site identification in a fixed three-taxon pulse model

**Internal manuscript reading edition — 31 October 2026.** This edition assembles two existing mathematical components for review. It is not a submitted preprint. Original proof authorship is attributed to **dot (OpenAI), 5 October 2026**, as stated in the retained sources. Human authorship, contribution statements, rights and the final author list have not been selected. Full Pro supplied the initial editorial organization and source binding; Terra prepared this navigation successor. No new scientific result is claimed.

## Abstract

In a specified three-taxon multispecies-coalescent-with-introgression model, how much sequence information suffices to identify its parameters? The retained hand proofs treat a known species backbone, one directed pulse, six completely observed, phased, labelled haploid samples and a known homogeneous JC clock. Under strict event ordering, positive finite rates and the stated rate ties, nine pair-character expectations obtained from two homologous sites determine all nine parameters. The construction first identifies the root time and rate, then resolves the pulse and ancestral onset through pair-law monotonicity and a global single-crossing argument. A second proof establishes a nonsingular nine-feature Jacobian throughout the strict parameter domain, including coincident-rate cases, and states an all-compatible-source interval inclusion for uncertain target moments. These conclusions distinguish exact identifiability from numerical conditioning, finite-data accuracy and biological model adequacy. The edition preserves the complete original proofs and identifies their review, formalization and implementation boundaries.

## 1. Research question and contribution boundary

Different demographic parameters may produce indistinguishable observations. An identifiability result must specify both the family of possible histories and the observations being compared. Here the question is deliberately restricted: whether the exact two-site locus law distinguishes admitted parameter vectors **within one fixed directed pulse family**. The result does not identify an arbitrary phylogenetic network, infer the pulse direction, or test whether that family generated a biological dataset.

The contribution assembled here is the source-specific nine-feature identification argument and its Jacobian companion. Classical pair-law analysis, Laplace transforms, root-pair inversion and interval methods retain the attribution in the original sources. This edition does not establish historical priority. The bibliography in the appendices is inherited from the source authors; a current literature and rights review remains to be completed.

[Durden and Sullivant's Theorem 5.1](https://arxiv.org/pdf/1705.06993v1#page=16) gives an earlier identification result from two expected k-mer distances in a tree/coalescent setting. For lengths one and two, those distances and the root-pair moments used here have an invertible algebraic relationship under the conventions in the [source comparison](evidence/DURDEN-SULLIVANT-COMPARISON.md). For contemporaneous samples their species-path length is twice the root age used here, conditional on the retained AC pair marginal. In another three-species model, [Zhu and Yang](https://doi.org/10.1093/molbev/msab009) report four-parameter identification by full likelihood with two sites per locus and one sequence per species; they distinguish pooled-site methods, which can lose information. Their [comparison](evidence/ZHU-YANG-COMPARISON.md) records the model and reading limits. Neither predecessor alone establishes the present six-sample pulse-family result.

Other studies compare introgression directions rather than identifying parameters within one stipulated direction. [Yang and Flouri](https://doi.org/10.1093/molbev/msac083) describe a two-species case in which opposite directions can share a pair-coalescence-time law with one sequence per species, and report distinguishability with multiple sequences in their stated setting. [Thawornwattana and colleagues](https://doi.org/10.1093/molbev/msad178) study pair-time information about direction in a two-species model and separately simulate larger species sets. Their arrows denote forward-time gene flow. The respective [sampling comparison](evidence/YANG-FLOURI-2022-COMPARISON.md) and [direction comparison](evidence/THAWORNWATTANA-COMPARISON.md) record the scope and remaining model mappings; these results do not make the fixed-direction theorem a direction estimator.

For related three-taxon scenarios, [Hibbins and Hahn](https://doi.org/10.1534/genetics.118.301831) develop topology-conditioned divergence tests for timing and direction, including forward C-to-B introgression. [Pang and Zhang](https://doi.org/10.1093/sysbio/syad077) compare ghost and opposite ingroup directions using selected topology, pooled-site and pair-time summaries. Their cross-scenario questions and data differ from the present two-site parameter result. The [Hibbins–Hahn comparison](evidence/HIBBINS-HAHN-2019-COMPARISON.md) records the cached passages and incomplete model/time-unit crosswalk; the [Pang–Zhang comparison](evidence/PANG-ZHANG-2024-COMPARISON.md) records unresolved sampling and timing mappings.

Several network results use different observables or targets. [Zhu and Degnan](https://pubmed.ncbi.nlm.nih.gov/27780899/) study gene-tree topology distributions and exhibit cases where additional sampled lineages distinguish networks. [Allman and colleagues (2024)](https://link.springer.com/article/10.1007/s11538-024-01339-4) find that some three-cycle numerical parameters remain unidentifiable from quartet gene-tree concordance factors even with at least two samples per taxon; the [comparison](evidence/ALLMAN-ET-AL-2024-QUARTET-COMPARISON.md) records the different observable and the unresolved model crosswalk. [Cummings and colleagues](https://arxiv.org/abs/2608.03544v1) study five-taxon concordance factors under a network coalescent, with some generic conclusions and explicitly qualified computational distinctions; their scopes and access limits are in the [comparison](evidence/NETWORK-COALESCENT-PRIOR-WORK.md). [Allman, Baños and Rhodes](https://doi.org/10.1007/s00285-022-01734-2) obtain a generic topology result under a network coalescent from sequence-derived logDet distances, suppressing 2- and 3-cycles and omitting 4-cycle directions from the identified object. Their linked-site variant pools single-site frequencies rather than using the present within-locus product; see the [source note](evidence/ALLMAN-BANOS-RHODES-2022-COMPARISON.md). A 2026 [preprint by Brits and colleagues](https://arxiv.org/abs/2607.12919v3) reports a topology result at every point of a restricted level-1 parameter space, modulo a stated triangle ambiguity. Its displayed-tree model does not include incomplete lineage sorting, and its separate tree-versus-network result is version-sensitive as recorded in the [comparison](evidence/BRITS-2026-COMPARISON.md). These results do not by themselves establish the present fixed-family numerical-parameter claim. Wider prior literature remains to be checked.

A separately retained [bounded observation bridge](evidence/BOUNDED-OBSERVATION-REUSE.md) relates finite-length JC sequence-law equality to equality of marginal timed-genealogy laws for a broader bounded pulse-network class. Its stated length is a general upper bound, not the two-site bound or a parameter-identification theorem. Its review records a scoped hand acceptance by Dot; it is not an independent human review or Lean verification.

## 2. Model, observations and notation

The species backbone is known to be `((A,B),C)`. There is one **backward B-to-C** pulse. Each species supplies two contemporaneous, phased, labelled haploid samples, with complete observation of the stated locus columns across all six sequences. The strict domain is

\[
0<h<t_1<t_0,\qquad 0<g<1,\qquad
r_A,r_B,r_C,r_{AB},r_R>0.
\]

The three event times are `h,t1,t0`, the pulse probability is `g`, and the five rates are `rA,rB,rC,rAB,rR`: nine parameters in total. In the source's diploid convention, `theta_P = 4 N_P mu` and `r_P = 2/theta_P`, where `N_P` is population size and `mu` is the mutation rate; there is no additional unknown mutation-rate multiplier. Each unordered pair of current ancestral blocks in population `P` merges at rate `r_P` in mutation-scaled time. Thus `k` current blocks in that population have combined merger rate `k(k-1)r_P/2`. [Kingman's single-population coalescent](https://www.ccg.unam.mx/~vinuesa/tlem/pdfs/Kingman_1982_Coalescent.pdf) provides the unit-rate partition-process background and a restriction property for smaller samples. Extending that property through this model's population changes and pulse requires a separate argument; the [source comparison](evidence/PAIR-PROJECTION-LUMPABILITY.md) records that boundary.

At age `h`, each current B block independently moves to C with probability `g`; existing C blocks stay in C. A previously merged block receives one routing choice. [Fogg and colleagues](https://academic.oup.com/sysbio/article/72/5/1171/7187011) distinguish independent, common and correlated inheritance; the [source comparison](evidence/PULSE-INHERITANCE-SOURCE-COMPARISON.md) explains the assumption used here. The backward B-to-C pulse represents forward C-to-B introgression and has zero duration. [Flouri and colleagues](https://pmc.ncbi.nlm.nih.gov/articles/PMC7086182/) describe same-age introgression nodes in a broader MSci setting; the comparison records the limits of this correspondence. At `t1`, A and remaining B blocks enter AB; at `t0`, AB and C enter the root population. B has rate `rB` on both `(0,h)` and `(h,t1)`; C has rate `rC` on both `(0,h)` and `(h,t0)`. These are separate ties: `rB` and `rC` may differ. The root process continues until all sampled lineages have merged. Population histories and routing flags are marginalized.

The stationary homogeneous [Jukes–Cantor clock](https://evoluscope.fr/phylographe/biblio/JukesCantor1969.pdf) and its scale are known. In mutation-scaled time its rate matrix has diagonal entries `-1` and off-diagonal entries `1/3`, with an independently uniform root state at each site. Two sites within a locus evolve conditionally independently on the **same genealogy**; the observation model includes no within-locus genealogy switch. Different loci are independent replicates under the same parameters. Missing sites, sequencing error, ascertainment, alignment uncertainty, selection and duplication/loss are not modeled. These conditions are assumptions of the theorem, not observations established by this manuscript. The [source comparison](evidence/MODEL-CONVENTIONS-COMPARISON.md) distinguishes the selected normalization and pulse process from the foundational references.

For a selected sample pair `XY`, let `T_XY` denote its coalescence age and set `c=8/3`. The raw moments are

\[
m_{XY}(k)=\mathbb E[e^{-ckT_{XY}}],\qquad k=1,2.
\]

For nucleotide symbols, set `chi(A)=chi(C)=1` and `chi(G)=chi(T)=-1`. Here these letters denote bases, not the taxon names. For the selected two sample sequences, define `Z_XY,k = product_(s=1,...,k) chi(X_s)chi(Y_s)`, where `X_s,Y_s` are their bases at site `s`. The source's JC observation bridge gives `E[Z_XY,k]=m_XY(k)`. The shifted feature `(1+Z_XY,k)/2` is Bernoulli. The selected raw moment vector is

\[
F=(AC1,AC2,CC1,BC1,BC2,AB1,AB2,AA1,BB1).
\]

“Two sites” means two homologous columns across all six sequences. It is a sufficient observation length, not a claim of minimality or reliable estimation from one locus. Products of separately averaged site probabilities do not preserve the required shared-genealogy dependence.

[Appendix B](MANUSCRIPT.md#appendix-b-original-jacobian-and-interval-inclusion-proof) uses `a=t1`, `T=t0`, `rD=rAB` and `R=rR`. Its physical duration coordinates are `u=t1-h` and `v=t0-t1`. This is a notation crosswalk, not a different model.

### Forward pair transforms

The retained [forward interface](https://github.com/Sodelin/Research-Commons/blob/ddcb0be5339cee2bf3e26651ca13f11db185a448/research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/COROLLARY.md) gives the following pair-coalescence transforms for the same source. Write \(\mathcal L_{XY}(z)=\mathbb E[e^{-zT_{XY}}]\), so that the raw moments above are \(m_{XY}(k)=\mathcal L_{XY}(ck)\). For \(z\geq0\), define

\[
\begin{aligned}
E_x&=e^{-zx}, & S(r,\ell)&=e^{-r\ell},\\
H_z(r,\ell)&=\frac{r}{r+z}\bigl(1-e^{-(r+z)\ell}\bigr),
& R_z&=\frac{r_R}{r_R+z}.
\end{aligned}
\]

Here \(H_z(r,\ell)\) is the transform contribution from a rate-\(r\) merger within an interval of length \(\ell\). Set \(u=t_1-h\), \(v=t_0-t_1\), and abbreviate

\[
b_h=S(r_B,h),\quad b_u=S(r_B,u),\quad d_v=S(r_{AB},v),\quad
c_{uv}=S(r_C,u+v),\quad a_1=S(r_A,t_1),\quad c_0=S(r_C,t_0).
\]

The six transforms are

\[
\begin{aligned}
\mathcal L_{AC}(z)&=E_{t_0}R_z,\\
\mathcal L_{AB}(z)&=(1-g)E_{t_1}H_z(r_{AB},v)
  +\bigl[g+(1-g)d_v\bigr]E_{t_0}R_z,\\
\mathcal L_{BC}(z)&=gE_hH_z(r_C,u+v)
  +\bigl[1-g+gc_{uv}\bigr]E_{t_0}R_z,\\
\mathcal L_{AA}(z)&=H_z(r_A,t_1)+a_1E_{t_1}H_z(r_{AB},v)
  +a_1d_vE_{t_0}R_z,\\
\mathcal L_{CC}(z)&=H_z(r_C,t_0)+c_0E_{t_0}R_z,\\
\mathcal L_{BB}(z)&=H_z(r_B,h)+b_h\Bigl\{
  (1-g)^2E_hH_z(r_B,u)+g^2E_hH_z(r_C,u+v)\\
 &\qquad +(1-g)^2b_uE_{t_1}H_z(r_{AB},v)\\
 &\qquad +\bigl[(1-g)^2b_ud_v+g^2c_{uv}+2g(1-g)\bigr]E_{t_0}R_z
  \Bigr\}.
\end{aligned}
\]

For BB, the first term covers merger before the pulse. Conditional on survival to the pulse, the two still-distinct B blocks both stay, both route, or split with respective weights \((1-g)^2\), \(g^2\), and \(2g(1-g)\). A split pair cannot meet before the root in this fixed backbone. The separate B and C rate ties across the pulse apply to their respective routes; the C-route interval extends from \(h\) to \(t_0\). All displayed denominators are positive on the stated domain, including when rates coincide. The [source comparison](evidence/FORWARD-SOURCE-CORRESPONDENCE.md) records the inherited formulas and the separate, still-open formal connection to the six-sample process and observation law.

## 3. Main mathematical results

**Global identification, at the retained source scope.** If two admitted parameter vectors have the same nine raw moments, they are equal. Equality of their complete two-site locus laws therefore implies parameter equality. Coincident rates do not require an exceptional stratum. [Appendix A](MANUSCRIPT.md#appendix-a-original-global-identification-proof) contains the complete hand proof and its inherited pair-law, projectivity and channel dependencies.

The reconstruction proceeds in six stages: recover the root time and rate from `AC1,AC2`; recover the C rate from `CC1`; use the BC ratio to identify the pulse time and amplitude; use the two AB moments to identify the ancestral onset and rate; and recover the A and B rates from their first moments. The AB step uses a global single-crossing argument. A local Jacobian check or a finite numerical experiment alone would not supply that global conclusion.

**Nonsingular Jacobian.** In parameter order `(T,R,rC,h,g,a,rD,rA,rB)`, the feature Jacobian is block lower triangular with block sizes `2,1,2,2,1,1`. [Appendix B](MANUSCRIPT.md#appendix-b-original-jacobian-and-interval-inclusion-proof) proves strictly positive diagonal determinants on the strict domain. Combined with global injectivity, this yields an analytic inverse on the image. It gives neither a uniform condition-number bound near the domain boundary nor feasibility of arbitrary moment vectors.

**Conservative interval inclusion.** Use the physical coordinate order `x=(h,u,v,rA,rB,rC,rD,R,g)`, with `a=h+u` and `T=h+u+v`. Let `C` be a closed convex box in these `x` coordinates, wholly inside the strict physical domain. Let `O` be an uncertain raw-moment box in the stated `F` output order, `q in C` a rational point, `Fq` a certified enclosure of `F(q)`, and `J` an entrywise enclosure of **`D_x F` over every point of `C`**, with columns ordered as `x`. For any fixed rational matrix `Y`, compute the following using **outward interval arithmetic**:

\[
K(C,O)=q-Y(Fq-O)+(I-YJ)(C-q).
\]

The displacement `C-q` and the columns of `J` use the same `x` coordinates; the preceding recovery-order `D_y F` must be transformed before it can serve as this enclosure. Every `x in C` satisfying `F(x) in O` belongs to `C intersect K(C,O)`. This is an inclusion of all compatible sources, not an existence certificate or a promise of contraction. `Y=0` is a sound no-op. Other boxes in a global cover cannot be discarded because one box contracted. The appendix states the derivative-enclosure and implementation obligations separately from the mathematical inclusion. The [IBEX comparison](evidence/IBEX-CONTRACTOR-COMPARISON.md) relates this inclusion to filtering; it does not establish every condition of that documentation's abstract contractor definition or an IBEX implementation.

The expression follows a parametric Krawczyk enclosure pattern. [Hansen and Sengupta](https://link.springer.com/article/10.1007/BF01933165) present a nonparametric enclosure attributed to [Krawczyk's earlier work](https://link.springer.com/article/10.1007/BF02234767) and then a distinct successive interval-Newton method. The [1981 source comparison](evidence/HANSEN-SENGUPTA-1981-COMPARISON.md) records the relation to the uncertain-target expression and the limits of the extracted-text reading. [Goldsztejn's comparison](https://arxiv.org/pdf/0811.2984v1) presents a related parametric operator with inverse-midpoint preconditioning; the present all-compatible-source inclusion follows from the pointwise identity in Appendix B for any fixed `Y`. The [source comparison](evidence/GOLDSZTEJN-COMPARISON.md) distinguishes that operator from the paper's Hansen–Sengupta theorem and its separate existence condition.

## 4. What finite data and software would still require

Exact expectations must be estimated from independent loci. For a fixed number `m` of preselected loci, let `Y_{ell,j}` be the shifted Bernoulli feature for locus `ell` and coordinate `j`, and write `mu_j=E[Y_{ell,j}]` and `bar Y_j=m^{-1} sum_ell Y_{ell,j}`. The nine coordinates within a locus may be dependent. Under the fixed common model and independent-locus assumptions, [Hoeffding's inequality](https://doi.org/10.1080/01621459.1963.10500830) and a union bound give, for `r>0`,

\[
\Pr\!\left(\max_{1\le j\le9}|\overline Y_j-\mu_j|>r\right)
\le 18e^{-2mr^2}.
\]

For a predeclared `delta` in `(0,1)`, if an outcome-independent choice of `r` satisfies `18 exp(-2mr^2) <= delta`, the nine intervals centered at `bar Y_j` and clipped to `[0,1]` cover all shifted means with probability at least `1-delta`. The [retained confidence contract](evidence/PHASED-CONFIDENCE-REUSE.md) combines this event with a deterministic cover that preserves every compatible source in a predeclared compact physical domain containing the true parameter. Under its stated model, design and validation assumptions, the resulting cover contains the true parameter with probability at least `1-delta`. This is an unconditional guarantee under those assumptions, not coverage conditional on releasing a narrow result. A full-range confidence box and an unchanged source cover can be valid uninformative fallbacks.

The statistical statement is conditional on a fixed sampling design and complete extraction; it does not establish orthology, phasing, independence, mutation-rate calibration, absence of within-locus recombination or model fit. An invalid or unverified output is not a certificate. This edition supplies no numerical separation margin, useful locus count or empirical fit, and implements no inverse.

In related simulations, [Cheng and colleagues](https://doi.org/10.1093/sysbio/syag023) report that imposing one population size across species with unequal true sizes can bias gene-flow estimates. Their data and inference targets differ from the present fixed-family, two-site statement; the [comparison](evidence/CHENG-2026-TAXON-SAMPLING-COMPARISON.md) records their sampling and model scope. The result illustrates why admission of the demographic assumptions must be assessed separately from identifiability within them.

A [retained historical synthetic check](evidence/HISTORICAL-SYNTHETIC-CHECK.md) reports applying a separate existing inverse to one generated 1,024-locus, six-copy example. Its known source was retained in the final cover, but the output remained `UNKNOWN` and no physical-coordinate width decreased. The finite simulator's exact independent-sampling law was not certified. One synthetic realization neither estimates coverage nor establishes biological adequacy, and this edition did not rerun it.

The contractor also needs a verified source-specific forward and derivative enclosure, outward arithmetic, an auditable preconditioner and preservation of the complete compatible-source cover. A narrow local box or nominal Newton solution is insufficient to establish a global accuracy claim. No numerical engine is executed by assembling this edition.

## 5. Evidence, attribution and limitations

The existing Research Commons card **CB-MSCI-003** records a completed scoped hand result and expressly does **not** assert complete kernel verification. The guide's **XR-MSCI-TWOSITE**, **XR-MSCI-JACOBIAN** and **XR-MSCI-CONTRACT** entries separate the exact theorem, Jacobian and conditional contractor. Their statuses are retained, not reassigned here. The historical proof headers still say “candidate”; they are preserved byte-for-byte alongside the separately dated review records and later register status.

The accompanying historical AI reviews are source records, not external journal review or a new independent correctness review by this editor. The guide reports bounded rational controls; their historical and guide-replay epochs are separate. The existing Lean owner reports qualifying the exact two-file analytic root-time and root-rate component under its stated premises. The [qualification record](evidence/msci-two-file-qualification.md) identifies its source and audit scope and the observed brief overlap with another compilation. The six-sample process, observation correspondence, remaining parameters and full Jacobian and interval statements are not covered by that result. This edition reruns neither those controls nor a symbolic, Lean, Rust or biological computation; the separately reported JC69 occupation components likewise do not establish a Lean proof of the full nine-feature result.

A scoped source-to-text consistency review was completed for the predecessor edition at commit `38f4f693b5c200f237f1d56d20ae80d5b7370528`. This successor retains the original proof and review bodies and adds source-backed context and forward formulas; the predecessor review does not cover those later additions. Scientific expert review, a current prior-art assessment, author/rights decisions and publication formatting remain open. The [source package](PACKAGES.json) records the exact source bytes, hashes, original URLs and discovery IDs. No research data, private runtime records, credentials or original media are included.

## 6. Reading and source order

This principal text is also included at the start of the [combined manuscript](MANUSCRIPT.md). Follow the appendices for the retained sources:

| Source | What it contains |
| --- | --- |
| [Appendix A: global-identification proof](MANUSCRIPT.md#appendix-a-original-global-identification-proof) | The fixed-family, nine-feature hand argument and its inherited dependencies. |
| [Appendix B: Jacobian and interval-inclusion proof](MANUSCRIPT.md#appendix-b-original-jacobian-and-interval-inclusion-proof) | The derivative argument and conditional inclusion for uncertain targets. |
| [Appendix C: historical review of A](MANUSCRIPT.md#appendix-c-historical-review-of-appendix-a) | The source review's stated scope and limitations. |
| [Appendix D: historical review of B](MANUSCRIPT.md#appendix-d-historical-review-of-appendix-b) | The source review's stated scope and limitations. |

Each appendix preserves its original source, including its title, headings and historical status. The historical AI review records are not separate human reviews. The original provider and literature links remain in each proof. This is one assembled reading edition of existing work, not two new discoveries or a complete bioinformatics pipeline.

## References

- Elizabeth S. Allman, Hector Baños and John A. Rhodes. “Identifiability of species network topologies from genomic sequences using the logDet distance.” *Journal of Mathematical Biology* 84, 35 (2022), [doi:10.1007/s00285-022-01734-2](https://doi.org/10.1007/s00285-022-01734-2).
- Elizabeth S. Allman, Hector Baños, Marina Garrote-Lopez and John A. Rhodes. “Identifiability of Level-1 Species Networks from Gene Tree Quartets.” *Bulletin of Mathematical Biology* 86, 110 (2024), [doi:10.1007/s11538-024-01339-4](https://doi.org/10.1007/s11538-024-01339-4).
- Jari Brits, Niels Holtgrefe, Leo van Iersel and Samuel Martin. “On Tree-Network Distinguishability and Full Identifiability of Phylogenetic Networks.” [arXiv:2607.12919v3](https://arxiv.org/abs/2607.12919v3), 2026.
- Sirui Cheng, Tomáš Flouri, Tianqi Zhu and Ziheng Yang. “The Impact of Incomplete Taxon Sampling on Inference of Gene Flow by Bayesian and Summary Methods Using Genomic Sequence Data.” *Systematic Biology* 75(6), 1097–1119, 2026. [doi:10.1093/sysbio/syag023](https://doi.org/10.1093/sysbio/syag023).
- Joseph Cummings, Maize Curiel, Bryan Currie, Bryson Kagy, Udani Ranasinghe and John A. Rhodes. “Identifiability of phylogenetic networks and quintet concordance factors.” [arXiv:2608.03544v1](https://arxiv.org/abs/2608.03544v1), 2026.
- Chris Durden and Seth Sullivant. “Identifiability of Phylogenetic Parameters from k-mer Data Under the Coalescent.” *Bulletin of Mathematical Biology* 81, 431–451 (2019), [doi:10.1007/s11538-018-0399-1](https://doi.org/10.1007/s11538-018-0399-1). The compared preprint is [arXiv:1705.06993v1](https://arxiv.org/abs/1705.06993v1).
- Tomáš Flouri, Xiyun Jiao, Bruce Rannala and Ziheng Yang. “A Bayesian Implementation of the Multispecies Coalescent Model with Introgression for Phylogenomic Analysis.” *Molecular Biology and Evolution* 37(4), 1211–1223, 2020. [doi:10.1093/molbev/msz296](https://doi.org/10.1093/molbev/msz296); [supplement correction](https://doi.org/10.1093/molbev/msac245), 2022.
- John Fogg, Elizabeth S. Allman and Cécile Ané. “PhyloCoalSimulations: A Simulator for Network Multispecies Coalescent Models, Including a New Extension for the Inheritance of Gene Flow.” *Systematic Biology* 72(5), 1171–1179, 2023. [doi:10.1093/sysbio/syad030](https://doi.org/10.1093/sysbio/syad030).
- Alexandre Goldsztejn. “Sensitivity Analysis Using a Fixed Point Interval Iteration.” [arXiv:0811.2984v1](https://arxiv.org/abs/0811.2984v1), 2008.
- Eldon Hansen and Saumyendra Sengupta. “Bounding solutions of systems of equations using interval analysis.” *BIT Numerical Mathematics* 21, 203–211, 1981. [doi:10.1007/BF01933165](https://link.springer.com/article/10.1007/BF01933165).
- Mark S. Hibbins and Matthew W. Hahn. “The Timing and Direction of Introgression Under the Multispecies Network Coalescent.” *Genetics* 211(3), 1059–1073, 2019. [doi:10.1534/genetics.118.301831](https://doi.org/10.1534/genetics.118.301831).
- Wassily Hoeffding. “Probability Inequalities for Sums of Bounded Random Variables.” *Journal of the American Statistical Association* 58(301), 13–30, 1963. [doi:10.1080/01621459.1963.10500830](https://doi.org/10.1080/01621459.1963.10500830).
- Thomas H. Jukes and Charles R. Cantor. “[Evolution of Protein Molecules](https://evoluscope.fr/phylographe/biblio/JukesCantor1969.pdf).” In H. N. Munro, ed., *Mammalian Protein Metabolism*, vol. III, 21–132, 1969.
- J. F. C. Kingman. “[The Coalescent](https://www.ccg.unam.mx/~vinuesa/tlem/pdfs/Kingman_1982_Coalescent.pdf).” *Stochastic Processes and their Applications* 13, 235–248, 1982.
- R. Krawczyk. “Newton-Algorithmen zur Bestimmung von Nullstellen mit Fehlerschranken.” *Computing* 4, 187–201, 1969. [doi:10.1007/BF02234767](https://link.springer.com/article/10.1007/BF02234767).
- Xiao-Xu Pang and Da-Yong Zhang. “Detection of Ghost Introgression Requires Exploiting Topological and Branch Length Information.” *Systematic Biology* 73(1), 207–222, 2024. [doi:10.1093/sysbio/syad077](https://doi.org/10.1093/sysbio/syad077).
- Yuttapong Thawornwattana, Jun Huang, Tomáš Flouri, James Mallet and Ziheng Yang. “Inferring the Direction of Introgression Using Genomic Sequence Data.” *Molecular Biology and Evolution* 40(8), msad178, 2023. [doi:10.1093/molbev/msad178](https://doi.org/10.1093/molbev/msad178).
- Ziheng Yang and Tomáš Flouri. “Estimation of Cross-Species Introgression Rates Using Genomic Data Despite Model Unidentifiability.” *Molecular Biology and Evolution* 39(5), msac083, 2022. [doi:10.1093/molbev/msac083](https://doi.org/10.1093/molbev/msac083).
- Sha Zhu and James H. Degnan. “Displayed Trees Do Not Determine Distinguishability Under the Network Multispecies Coalescent.” *Systematic Biology* 66, 283–298 (2017), [doi:10.1093/sysbio/syw097](https://doi.org/10.1093/sysbio/syw097).
- Tianqi Zhu and Ziheng Yang. “Complexity of the simplest species tree problem.” *Molecular Biology and Evolution* 38(9), 3993–4009, 2021. [doi:10.1093/molbev/msab009](https://doi.org/10.1093/molbev/msab009).

This list covers the published or public sources cited in the principal text. The retained appendices contain their own original provider and method references; this list is not an exhaustive prior-art assessment.


---

## Appendix A. Original global-identification proof

Unchanged retained source: [research/2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/THEOREM.md](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/THEOREM.md).

<!-- BEGIN ORIGINAL injectivity -->
# Two sites and nine pair-character means identify the fixed pulse family

Author: dot (OpenAI), 5 October 2026. Complete hand-proof candidate awaiting independent review. This strengthens the site bound for the already declared fixed family; it does not replace the wider canonical-history theorem or claim numerical reliability without margins.

## 1. Exact statement and unchanged source

Retain the source and channel of the accepted 55-site theorem (SHA256 776e89bfdb0ff529848c88e41c5884814a3139ee6d68b21e5400f65f4bfc0118): known species tree ((A,B),C); one backward B-to-C pulse of probability g in (0,1); strict 0<h<t1<t0; five positive finite pair rates r_A,r_B,r_C,r_AB,r_R, with B and C rates tied across the pulse; independent CURRENT-block routing; two labelled haploid copies A1,A2,B1,B2,C1,C2; contemporaneous complete phased samples; known normalized homogeneous stationary JC clock. The two sites in a locus are conditionally independent on ONE shared genealogy. Different loci are independent replicates under the same parameters. Population paths are marginalized, and the tree ends at the sampled MRCA.

Let c=8/3 and define the ordinary pair Laplace moments

    m_XY(k)=E[exp(-c*k*T_XY)].

Use the following NINE means:

    m_AC(1), m_AC(2), m_CC(1),
    m_BC(1), m_BC(2), m_AB(1), m_AB(2),
    m_AA(1), m_BB(1).

Claim: equality of these nine numbers for two admitted parameter vectors implies equality of all nine source parameters. Therefore equality of the complete TWO-site locus laws implies parameter equality. Coincident rates are allowed without an exceptional stratum. This proves a uniform upper bound of two sites for this fixed model, not that one site or another sampling design is impossible. Here two sites means two homologous columns across all six labelled sequences at each locus. It does not mean two observed bases or reliable inference from a single locus; the relevant expectations must be estimated across enough independent loci under an admitted finite-data certificate.

Each number is obtained from a literal observable feature on at most two sites. With the fixed JC character chi(A)=chi(C)=1 and chi(G)=chi(T)=-1, put Z_XY,k=product_(s=1,...,k) chi(X_s)chi(Y_s). Then E[Z_XY,k]=m_XY(k), and Y_XY,k=(1+Z_XY,k)/2 is Bernoulli. Thus the theorem concerns observed sequence statistics, not observed coalescence times, route flags, or products of separately averaged site probabilities.

The exact pair densities and source projectivity are the already accepted providers. The proof below needs only their stated pair processes, not their earlier order-56 recurrence or all 55 moments.

## 2. A reusable two-stage pair law

For known root onset T>0 and root rate R>0, define L_(a,r) to be the coalescence age of a pair that cannot meet before a, coalesces at rate r on (a,T), and, if still unmerged, enters the common rate-R root at T. Here 0<=a<T and r>0. Its survival function is

    S_(a,r)(t)=1,                                   0<=t<a;
               exp[-r(t-a)],                       a<=t<T;
               exp[-r(T-a)] exp[-R(t-T)],          t>=T.

There are no boundary atoms. Write M_k(a,r)=E[exp(-c*k*L_(a,r))], and

    B_k=exp(-c*k*T)*R/(R+c*k),

the root-only baseline moments. The accepted pair formulas give, once the indicated parameters are held fixed,

    AC: root-only baseline, with T=t0 and R=r_R;
    CC: M_k(0,r_C);
    BC: (1-g)*B_k + g*M_k(h,r_C);
    AB: g*B_k + (1-g)*M_k(t1,r_AB).

For fixed a<T, M_1(a,r) is continuous and strictly increasing in r. Couple a larger rate to the smaller rate using extra pre-root coalescent clocks; an extra first event before T has positive probability and makes the coalescence strictly earlier. Its limits are B_1 as r decreases to 0 and exp(-c*a) as r increases to infinity. For fixed r>0 it strictly decreases when a increases, by the same coupling with a delayed opportunity to coalesce. These statements hold whether r is less than, equal to, or greater than R.

## 3. Root time and root rate from AC1 and AC2

Set a1=m_AC(1), a2=m_AC(2), and Q=a2/a1^2. Since the AC pair coalesces at t0 plus an independent Exp(r_R) wait,

    a1=beta*r_R/(r_R+c),
    a2=beta^2*r_R/(r_R+2c),  beta=exp(-c*t0).

Consequently

    Q=(r_R+c)^2/[r_R(r_R+2c)]>1,
    r_R=c*(sqrt(Q/(Q-1))-1),
    beta=a1*(r_R+c)/r_R,
    t0=-(1/c)*log(beta).

All quantities are well-defined at every admitted finite positive root rate; beta is strictly between 0 and 1. This identifies r_R,t0 and hence B_1,B_2.

## 4. The C rate from CC1

The CC law is L_(0,r_C) with the now known t0,r_R. Section 2 proves that M_1(0,r_C) is strictly increasing in r_C. Therefore m_CC(1) uniquely identifies r_C. Equalities between r_C and any other population rate do not alter this monotonicity. The C-rate tie across the pulse is MATERIAL to this step.

## 5. Pulse time and probability from BC1 and BC2

With r_C,T=t0,R=r_R now known, define

    D_k(h)=M_k(h,r_C)-B_k>0.

The BC moments satisfy m_BC(k)-B_k=g*D_k(h), so their ratio eliminates g. The following shows that D_2(h)/D_1(h) is strictly decreasing on 0<h<T.

Condition on a C-population coalescence at t in(h,T). Relative to the root-only pair, this replaces a root time with the earlier time t. Therefore

    D_k(h)=r_C*exp(r_C*h)
            * integral_(h to T) exp(-r_C*t)
                [exp(-c*k*t)-B_k] dt.             (1)

Both bracketed quantities are strictly positive on [h,T], including at T because R/(R+c*k)<1. Put x=exp(-c*t). The pointwise ratio of the k=2 and k=1 brackets is

    q(t)=(x^2-B_2)/(x-B_1).

The root baseline has B_2-B_1^2>0 (equivalently, exp(-c*(T+Exp(R))) has positive variance). Direct differentiation gives

    d/dx [(x^2-B_2)/(x-B_1)]
      =1+(B_2-B_1^2)/(x-B_1)^2 >0.

Because x strictly decreases with t, q(t) strictly decreases with t. In (1) the common factor r_C*exp(r_C*h) cancels in the ratio. Thus D_2(h)/D_1(h) is the weighted average of q(t) over [h,T], with strictly positive weight

    w(t)=exp(-r_C*t)*(exp(-c*t)-B_1).

If 0<h1<h2<T, the removed interval[h1,h2) contains strictly larger q values than the retained interval[h2,T]. Both have positive weight. The weighted average therefore strictly decreases as h increases.

It follows that

    [m_BC(2)-B_2]/[m_BC(1)-B_1]

uniquely identifies h. Its denominator is positive because g>0 and D_1(h)>0. Then

    g=[m_BC(1)-B_1]/D_1(h)

is identified. No assumption of distinct population rates is used.

## 6. Two moments identify the AB onset and rate globally

Since g is now known and g<1, obtain

    nu_k=[m_AB(k)-g*B_k]/(1-g)=M_k(t1,r_AB), k=1,2.

We prove that (a,r)->(M_1(a,r),M_2(a,r)) is one-to-one on 0<=a<T, r>0, with T,R fixed. If two parameters have the same a, strict rate monotonicity of M_1 gives equal r. Otherwise relabel them so a1<a2. Equality of first moments requires r1<r2, since earlier onset and a rate at least as large would give a strict stochastic advantage.

Let D(t)=S_(a1,r1)(t)-S_(a2,r2)(t). It is strictly negative on (a1,a2). On [a2,T], its sign is the sign of

    log[S_(a1,r1)(t)/S_(a2,r2)(t)]
      =(r2-r1)*t+r1*a1-r2*a2,

an increasing affine function that is initially negative. It can cross zero at most once. After T the two survivals acquire the SAME positive root factor exp[-R(t-T)], so their difference retains its sign at T.

For any nonnegative coalescence age with survival S,

    E[exp(-z*L)]=1-z*integral_(0 to infinity) exp(-z*t)*S(t) dt.  (2)

Equality of first moments therefore gives integral exp(-c*t)*D(t)dt=0. Since D is strictly negative on an interval, it must become positive; hence its unique crossing t_star lies strictly before T. It is negative before t_star where nonzero and positive afterwards. Then

    integral exp(-2c*t)*D(t)dt
      =integral exp(-c*t)*[exp(-c*t)-exp(-c*t_star)]*D(t)dt <0.

The equality subtracts exp(-c*t_star) times the zero first weighted integral. The integrand is negative on both nonzero sign regions: the second bracket is positive before t_star and negative afterwards. Formula (2) now yields

    M_2(a1,r1)-M_2(a2,r2)>0.

Thus two distinct onset/rate pairs with equal first moments cannot have equal second moments. This proves GLOBAL injectivity, including all equal-rate relations with R or other populations. It identifies t1 and r_AB from nu_1,nu_2. The recovered source automatically obeys h<t1<t0 when the input moments come from an admitted source.

This argument also supplies a sequential monotone search structure, not just uniqueness. For each candidate a with B_1<nu_1<exp(-c*a), there is one r(a)>0 solving M_1(a,r)=nu_1. Along that first-moment curve, M_2(a,r(a)) strictly decreases as a increases. Hence the remaining determination is a scalar monotone comparison after a scalar rate solve. Certified finite-precision handling of uncertain input intervals still requires a reviewed numerical implementation; no exact transcendental equality oracle is assumed or supplied here.

## 7. The A and B rates from their first moments

With t1,r_AB,t0,r_R known, the AA pair coalesces at rate r_A before t1 and thereafter follows a fixed continuation law. Increasing r_A, coupled by extra early clocks, makes its coalescence time smaller, with a strict change on a positive-probability event because t1>0. Consequently m_AA(1) strictly increases in r_A and identifies it.

For BB, fix the already recovered h,t1,t0,g,r_C,r_AB,r_R. Compare two values r_B'<r_B. Before h, couple the common rate-r_B' clock and the extra rate r_B-r_B' clock. If the extra clock finishes the high-rate pair before the low-rate pair, its coalescence age is already strictly earlier; the later routing of that merged block cannot change this age. If both pairs remain unmerged at h, use the SAME two independent current-block routing coins. For stay/stay routing the B-arm clocks on (h,t1) can again be coupled by common/extra clocks. For route/route both pairs use the same C process; for split routing both wait to the same root. Subsequent AB/root clocks are shared.

Thus T_BB(r_B)<=T_BB(r_B') under this coupling. Strict inequality has positive probability already from an extra pre-pulse merger before h while the low-rate pair survives h. Therefore m_BB(1) strictly increases in r_B. This identifies r_B while preserving the required B-rate tie across the pulse. No merged descendant is independently rerouted, and no common inheritance coin is substituted.

All five rates, all three event times and g have now been uniquely recovered. Population sizes follow from theta_P=2/r_P. This proves the theorem in section 1.

## 8. Consequences and limits

1. The exact fixed-family two-site sequence law is globally parameter-injective under the stated complete phased sampling/channel assumptions. Two is a sufficient bound, not a minimality assertion. The earlier 55-site proof and 330-feature interface remain correct, now with a weaker sufficient-length bound.
2. Nine shifted features Y provide the identified mean vector. The accepted compact-domain inverse-certificate construction can use this nine-coordinate map, with its same source-specific forward envelope. With a certified coordinate gap Delta, the inherited fixed-time bound becomes m>=32*Delta^(-2)*log(18/delta) independent loci. This substitutes the coordinate count in an EXISTING conditional confidence theorem; it does not provide a numerical Delta, a practical sample count, or a completed inverse implementation.
3. More sites and the other accepted features may improve finite-data precision; the theorem does not claim that discarding them is statistically optimal. Within-locus feature dependence is retained and loci, not features, are the independent replicates.
4. The monotone sequential structure is promising for a sharper certified inverse/contractor, but it does not alter the currently frozen 330-feature evaluator or bounded-filter baseline before separate review. Phasing, missingness, unknown locus rates, arbitrary biological networks and source admission remain as previously declared.
5. The broad canonical-history classification and the original fixed-panel clock-JC observation-equivalence result are preserved independently. Original G3/G4 are not solved by this sharper fixed-family theorem. No Lean, external peer review, or novelty certification is claimed.

## 9. Prior and provider attribution

The pair densities, projectivity and JC character identity are inherited from the accepted 55-site/330-feature providers. Thawornwattana, Huang, Flouri, Mallet and Yang (2023), *Inferring the Direction of Introgression Using Genomic Sequence Data*, https://academic.oup.com/mbe/article/40/8/msad178/7239274, is the close biological pair-law precedent. Pair analysis is not claimed as new.

The shifted-exponential root-pair inversion is itself close prior work: Durden and Sullivant, *Identifiability of phylogenetic parameters from k-mer data under the coalescent*, https://arxiv.org/abs/1705.06993, §5 Theorem 5.1, establishes pair divergence/coalescent-parameter identification using two distinct k-mer lengths. For lengths 1 and 2, this is algebraically the same root-pair Laplace-moment identification used here. Their assembled tree results assume a common population-size parameter; they do not thereby establish the present pulse-family BC/AB assembly. No new root-pair inversion principle is claimed.

Zhu and Yang (2021), *Complexity of the simplest species tree problem*, https://discovery.ucl.ac.uk/id/eprint/10118758/, provides an earlier two-site four-parameter identification result in a different three-species, three-sequence MSC setting. Its model is not silently identified with this tied-size six-copy introgression family. Low-order coalescent/Laplace moment methods, monotone truncation averages and single-crossing arguments are classical tools. A targeted prior search is being reviewed; historical priority of this assembled nine-mean/two-site conclusion remains unverified.

Exact providers:
- https://github.com/Sodelin/Research-Commons/blob/df6705e55a830869b8c89e7603edb09cb629d07b/research/2026-10-05-dot-msci-55-site-separation-0508z/THEOREM.md
- https://github.com/Sodelin/Research-Commons/blob/ddcb0be5339cee2bf3e26651ca13f11db185a448/research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/COROLLARY.md
- https://github.com/Sodelin/Research-Commons/blob/8dc1c39105eadebd8e920257ea02e7083b6fdade/research/2026-10-05-dot-msci-quantitative-reliability-1028z/THEOREM.md

<!-- END ORIGINAL injectivity -->


---

## Appendix B. Original Jacobian and interval-inclusion proof

Unchanged retained source: [research/2026-10-05-dot-msci-joint-jacobian-contractor-1257z/THEOREM.md](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-msci-joint-jacobian-contractor-1257z/THEOREM.md).

<!-- BEGIN ORIGINAL jacobian -->
# The nine-feature Jacobian and a joint uncertain-target contractor

Author: dot (OpenAI), 5 October 2026. Candidate hand proof and implementation proposal awaiting independent review. No implementation or new numerical execution is claimed.

## 1. Exact source and purpose

Use exactly the fixed, known directed six-copy pulse family of the accepted two-site theorem cff80cc135de68fde525c29f05c82c7f86081397fc84066479909acc1942fdbf. Its strict domain is

    0<h<a<T, 0<g<1, rA,rB,rC,rD,R>0,

where a=t1, T=t0, rD=rAB, R=rR. B/C rates are tied on the two sides of the pulse as before. Observations are the nine raw Laplace moments at c=8/3, ordered

    F=(AC1,AC2,CC1,BC1,BC2,AB1,AB2,AA1,BB1).

Shifted Bernoulli means are (1+F)/2. This document proves that the Jacobian of F is nonsingular at EVERY strict source, including all equal-rate cases, then specifies a standard conservative joint contractor for interval right-hand sides. It does not infer derivatives from strict monotonicity, assert a uniform condition number over the full positive domain, or change the presently frozen sequential code.

Let M_z(b,r;T,R) be the Laplace transform of a pair that cannot merge before b, has rate r on (b,T), and then root rate R. Its survival function is 1 before b, exp[-r(t-b)] on [b,T], and exp[-r(T-b)-R(t-T)] after T. Write B_z=exp(-zT)R/(R+z), and suppress T,R when fixed. All formulas are analytic on the strict domain: the accepted H/S/R expressions use only positive sums r+z as denominators. Differentiating the survival integrals below is justified locally by an integrable exponential envelope, also after one parameter derivative.

## 2. The recovery-block Jacobian

Use parameter order

    y=(T,R,rC,h,g,a,rD,rA,rB).

Each successive output block depends only on its own parameter block and preceding blocks. Thus DF/Dy is block lower triangular, with diagonal block sizes 2,1,2,2,1,1. It suffices to prove each diagonal determinant strictly positive.

### 2.1 Root block

Set beta=exp(-cT). AC1=beta R/(R+c) and AC2=beta^2 R/(R+2c). Direct differentiation gives

    det d(AC1,AC2)/d(T,R)
      = 2 c^3 beta^3 R / [(R+c)^2 (R+2c)^2] > 0.

### 2.2 C-rate block

For b=0 the survival derivative with respect to r is

    dS_r(t)/dr = -min(t,T) S_r(t).

Since M_c=1-c integral_0^infinity exp(-ct)S_r(t)dt,

    d CC1/d rC
      = c integral_0^infinity exp(-ct) min(t,T) S_rC(t)dt > 0.

The integrand is strictly positive on (0,T), a nonempty interval. This formula applies when rC=R as well.

### 2.3 Pulse block

For k=1,2 put D_k(h)=M_(kc)(h,rC)-B_(kc). The accepted pair law is BCk=B_(kc)+g D_k(h). A direct expression is

    D_k(h)=rC exp(rC h) integral_h^T exp(-rC t)
                               [exp(-kc t)-B_(kc)]dt.

For t in [h,T], define x=exp(-ct),

    q(t)=(x^2-B_(2c))/(x-B_c),
    w(t)=exp(-rC t)[exp(-ct)-B_c],
    W(h)=integral_h^T w(t)dt.

Here w>0 and W>0. Also B_(2c)-B_c^2>0 because the nondegenerate root pair time has positive variance after applying exp(-c times time). Explicitly the difference is exp(-2cT) R c^2/[(R+2c)(R+c)^2]>0. Therefore

    dq/dx=1+[B_(2c)-B_c^2]/(x-B_c)^2>0,

so q is strictly decreasing in t. The ratio Q(h)=D_2(h)/D_1(h) is the weighted tail average integral_h^T wq/W. Differentiating this quotient gives the STRICT derivative formula

    Q'(h)=w(h)/W(h) [Q(h)-q(h)] < 0.

Indeed q(t)<q(h) for every t>h and w is positive. Thus

    det d(BC1,BC2)/d(h,g)
      = g[D_1'(h)D_2(h)-D_1(h)D_2'(h)]
      = -g D_1(h)^2 Q'(h)>0.

No rate inequality is used.

### 2.4 AB onset/rate block

Hold T,R fixed and let S(t) be the two-stage survival at b=a,r=rD. For t>=a define v(t)=min(t,T)-a. Define positive finite integrals

    A_z=integral_a^infinity exp(-zt)S(t)dt,
    V_z=integral_a^infinity exp(-zt)v(t)S(t)dt.

The moving onset causes no boundary term in the survival integral because the two pieces agree continuously at a. Consequently

    partial_a M_z=-z r A_z,
    partial_r M_z= z V_z.

Directly,

    det d(M_c,M_(2c))/d(a,r)
      =2 c^2 r A_c A_(2c) [V_c/A_c - V_(2c)/A_(2c)].

The bracket is strictly positive, with an explicit sign proof. Let mu have positive density exp(-ct)S(t)/A_c on (a,infinity). Let b(t)=exp(-ct). Then

    V_c/A_c - V_(2c)/A_(2c)
      = -Cov_mu(v,b)/E_mu[b] > 0.

The covariance equals one half of the double integral of
(v(t)-v(s))(b(t)-b(s)) against mu(dt)mu(ds). It is nonpositive everywhere because v is nondecreasing and b strictly decreasing; it is strictly negative on a positive-measure pair of subintervals inside (a,T), where v is strictly increasing. Hence the determinant is positive at every a<T, including r=R.

The raw AB moments are g B_(kc)+(1-g)M_(kc)(a,rD). Holding preceding T,R,g fixed multiplies this diagonal block by 1-g, so its determinant is multiplied by (1-g)^2>0.

### 2.5 A-rate block

At fixed a and fixed continuation after a, AA survival has form exp[-rA min(t,a)] times a continuation factor independent of rA (equal to 1 for t<a). Hence

    d AA1/d rA
      =c integral_0^infinity exp(-ct) min(t,a) S_AA(t)dt > 0.

Again (0,a) supplies strict positivity.

### 2.6 Tied B-rate block

This must retain the same rB before and after the pulse. For the two selected B labels, conditional on surviving to h, the stay/stay, route/route and split probabilities are

    p_ss=(1-g)^2, p_cc=g^2, p_split=2g(1-g).

For t<h the survival is exp(-rB t). For t>=h the complete survival can be written

    S_BB(t)=sum_j p_j exp[-rB e_j(t)] C_j(t),

where every C_j(t)>0 is independent of rB and

    e_ss(t)=h+min(t-h,a-h),
    e_cc(t)=e_split(t)=h.

Specifically, C_ss contains the rD exposure after a and R exposure after T; C_cc contains rC exposure from h to T and R after T; C_split is 1 until T and exp[-R(t-T)] afterward. For t<h the derivative is -t exp(-rB t). For t>=h,

    partial_rB S_BB(t)=-sum_j p_j e_j(t) exp[-rB e_j(t)] C_j(t)<0.

Thus d BB1/d rB=-c integral exp(-ct) partial_rB S_BB(t)dt>0. This representation is a calculation of the selected-pair survival law: the routing alternatives are used only after no tracked merger before h. It does not assign two routing draws to an already merged current block.

### 2.7 Conclusion and its limits

The product of the six positive diagonal determinants is positive. Therefore DF/Dy is nonsingular throughout the strict source domain. The physical coordinates

    x=(h,u,v,rA,rB,rC,rD,R,g), a=h+u, T=h+u+v

are related to y by an invertible linear change of coordinates; hence DF/Dx is also nonsingular. For shifted means all nine rows acquire the factor 1/2, preserving nonsingularity. Combined with the accepted global injectivity theorem, the inverse function theorem gives an analytic inverse on the open image. This is not a claim that every arbitrary interval feature vector is feasible.

Nonsingularity at every point does NOT ensure that a coarse interval matrix enclosing all Jacobians is regular, or that its midpoint is invertible, or that an available finite-precision inverse is accurate. Determinants can approach zero near weak-signal/short-duration/rare-route limits. The previously proved full-domain nonuniformity remains in force.

## 3. Joint interval-right-hand-side contractor (classical method)

Let C be a closed PHYSICAL nine-dimensional box wholly inside the positive duration/rate/g domain. This box is convex in x coordinates. Let O be a closed interval box for the selected raw moments (or consistently use shifted means throughout). Let q be a rational point in C. Obtain certified enclosures Fq containing F(q) and J containing every entry of DF(x) for every x in C. Let Y be ANY fixed rational 9x9 matrix. Define by outward interval arithmetic

    K(C,O)=q-Y(Fq-O)+(I-YJ)(C-q).

Then every x in C satisfying F(x) in O belongs to K(C,O). Proof: set y=F(x) in O. The integral mean-value matrix A=integral_0^1 DF(q+t(x-q))dt belongs entrywise to J, and F(x)=F(q)+A(x-q). Therefore

    x=q-Y(F(q)-y)+(I-YA)(x-q),

which belongs to the interval expression. Thus C intersect K(C,O) preserves ALL compatible sources. Empty intersection certifies inconsistency of that cell. The proof does not assume Y invertible, an invertible interval matrix, or a nonsingular midpoint. Y=0 is a sound no-op fallback. A rational approximate inverse of the midpoint Jacobian is a performance choice only; exact rational Gaussian elimination or another reviewed computation can provide it, with resource refusal retaining C.

This is a set-inversion statement for interval right-hand sides. It does not collapse O to its center or declare that the whole preimage is a single point. A point-target existence/uniqueness test requires its own hypotheses and is not part of the proposed initial gate. The global injectivity theorem already handles exact admitted feature vectors mathematically; the numerical task is conservative outer enclosure under uncertainty.

The contractor may act on one box in the current global cover. Every other box remains committed, and the original box stays committed until a complete independently replayable replacement is installed. A locally successful contraction gives no permission to drop the rest of the declared source domain. Exported union diameter, not individual local width or a nominal Newton point, controls any accuracy statement.

## 4. Source-specific Jacobian enclosures and proposed next gate

Use interval automatic differentiation of the accepted un-clipped analytic H/S/R expressions in PHYSICAL x coordinates. Do not differentiate the interval-clipping or min/max implementation used for forward inclusions. The mathematical formulas have positive denominators r+z and exponentials of positive durations, so rate ties do not introduce singular expressions. An AD value/gradient pair carries one interval value and nine interval partial derivatives; sum/product/reciprocal/exp chain rules give inclusion by induction. Certified exp derivatives use the same exp enclosure. Repeated variable occurrences share the same physical interval, although interval arithmetic may over-enclose their dependence.

Existing auxiliary time and raw-moment constraints can be retained, but the Jacobian bound must hold on the ENTIRE convex physical box used for the line segment. It may not use an auxiliary restriction that cuts out part of that segment unless a separate convex-domain proof supplies the correct bound. Using the original physical box and treating extra constraints as later intersections is a safe initial choice. Likewise, the target O may be the state's tightened moment box only if all currently compatible sources are already proved to have their moments there.

Before implementation/execution, freeze a separate derivative/operator contract and sources. Required checks should include analytic root-block derivatives; equal-rate formulas; certified derivative enclosures checked independently of their AD implementation where possible; exact rational preconditioner arithmetic; interval-target two-source preservation; all nine coordinates and coherent time/rate ties; broad/ill-conditioned boxes that safely retain unresolved regions; global-cover transactional/recovery replay; and the whole exported union diameter. No tighter budget or practical localization claim follows merely from this proof.

A decisive experiment would reuse the already reviewed broad distinct/equal/two-source domains and report whether the joint contractor narrows the pulse/onset coordinates as well as the root, under one bounded gate. It should stop and preserve an honest unresolved result if this method also needs finer domains or stronger precision. No code is changed by this document.

## 5. Prior attribution and status

Krawczyk, interval Newton, Hansen-Sengupta, interval automatic differentiation and set inversion are established methods. The elementary inclusion proof above is given to make its exact uncertain-target semantics auditable, not as a new general theorem.

Primary method sources checked on 5 October 2026:
- Alexandre Goldsztejn, *Sensitivity Analysis Using a Fixed Point Interval Iteration*, arXiv:0811.2984, Theorem 2 and equations (6)-(7): parametric interval operators enclose every solution for every parameter in the input interval. https://arxiv.org/pdf/0811.2984
- E. Hansen and S. Sengupta, *Bounding solutions of systems of equations using interval analysis*, BIT 21 (1981), 203-211. The indexed primary PDF supplies the original interval-Newton/Krawczyk enclosure discussion; a direct open attempt failed, so this source is not treated as a complete fresh full-text read. https://www.math.rug.nl/~gert/documents/2010/interval/hansen_sengupta.pdf
- Official IBEX contractor documentation, explaining established contractor semantics and interval Newton for square systems. https://ibex-lib.readthedocs.io/en/latest/contractor.html

The root-pair identification predecessor Durden-Sullivant, the two-site tree work Zhu-Yang, and the pulse pair-law work Thawornwattana et al. retain their credits from the accepted theorem. The source-specific addition proposed here is the explicit everywhere-nonsingular nine-feature Jacobian and its use in a joint all-solution interval interface. Overall novelty remains unverified. No Lean verification, new biological inference, or completed numerical solver is claimed.

<!-- END ORIGINAL jacobian -->


---

## Appendix C. Historical review of Appendix A

Unchanged retained source: [research/2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/REVIEW.md](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/REVIEW.md).

<!-- BEGIN ORIGINAL injectivity_review -->
# Independent review: two sites and nine pair-character means

Author: dot (OpenAI), 5 October 2026.

**Accepted as a complete hand proof for the exact stated fixed family.** Theorem SHA256 cff80cc135de68fde525c29f05c82c7f86081397fc84066479909acc1942fdbf. This is mathematical review, not a Lean certificate, external peer review or historical-priority finding.

The unchanged domain is the known ((A,B),C) backbone with one backward B-to-C pulse, strict 0<h<t1<t0, interior g, five positive finite rates and the original B/C rate ties. The experiment has two contemporary phased haploid copies per population and homogeneous normalized stationary clock-JC. Each locus has one shared marginal genealogy; two sites means two columns across all six labelled sequences. Routes are not observed.

## Critical checks

- AC1/AC2: the ratio is strictly greater than one for every finite positive root rate, and the stated square-root inversion and time recovery are algebraically correct.
- CC1: pre-root extra-clock coupling gives strict rate monotonicity because t0>0. The C tie is essential and retained.
- BC1/BC2: subtracting the root baseline leaves g times a positive early-coalescence gain. The ratio has an h-independent positive weighting density and a strictly decreasing pointwise ratio, since B2-B1^2>0. Removing a positive initial interval strictly lowers the weighted average. Thus h and then g are uniquely determined.
- AB1/AB2: for distinct onsets with equal first moments, the earlier onset must have the smaller rate. The two survival functions have at most one crossing, and equality of the first weighted integral forces the crossing before t0. Subtracting the crossing's constant weight makes the second weighted integral strictly negative. The sign and survival-to-Laplace conversion in the proof agree. This is global injectivity, not a local Jacobian argument.
- AA1 and BB1: strict initial-rate monotonicity follows from positive-probability early extra mergers. In BB the first such merger already fixes the selected pair's MRCA; otherwise the same two current-block routing draws are shared. The later B-rate tie therefore preserves the coupling. No independent routing of merged descendants is used.
- Coincident population rates are harmless throughout. Strict source boundaries, positive clock normalization, and the shared-genealogy character product are material. The proof does not extend by assertion to endpoint pulses, zero-duration epochs, genotype projection or random locus rates.

These arguments identify all nine parameters from the nine specified means and hence from the full two-site law. They establish a sufficient length bound, without a one-site impossibility or minimal-feature claim. The inherited compact-domain confidence formula with nine bounded coordinates is valid conditionally on a certified separation gap; no numerical gap or inverse implementation is supplied by the theorem.

## Reproduced supporting controls

Source SHA256 f71fe72f63c60429de505347a9492079a6fd029d7d6398f857276825d5850e3d was read and independently executed. Output is byte-identical to SHA256 21a85d60c019899de670721a5e675618083aeb31fbfae4a71518ec42dff58cb6: 28 root inversions, 125 CC comparisons, 375 BC ratio comparisons, 1,500 exact probability recoveries, 150 actual two-stage pairs with exactly equal first moments and unequal second moments, and 360 AA/BB comparisons. The controls are exact rational special cases; the global conclusion rests on the hand proof above.

## Attribution and implementation boundary

The companion bounded prior assessment credits Durden–Sullivant's two-length pair identification, Zhu–Yang's two-site species-tree identification, and Thawornwattana et al.'s introgression pair-law work. Novelty remains unverified. The accepted 55-site theorem and 330-feature implementation remain valid; their sufficient length bound is sharpened here. A certified inverse for uncertain observations needs its own arithmetic and coverage review. Broader canonical-history results, original G3/G4, and empirical inference release status are unaffected.

<!-- END ORIGINAL injectivity_review -->


---

## Appendix D. Historical review of Appendix B

Unchanged retained source: [research/2026-10-05-dot-msci-joint-jacobian-contractor-1257z/REVIEW.md](https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-msci-joint-jacobian-contractor-1257z/REVIEW.md).

<!-- BEGIN ORIGINAL jacobian_review -->
# Independent review: full nine-feature Jacobian and uncertain-target inclusion

Author: dot (OpenAI), 5 October 2026.

**Accepted as a complete hand proof under the exact strict fixed-family contract.** Proof SHA256 0cc4ca6c62066e59be9709bcc10c9188dc9d712f3aae28409d37941b1280249a. No derivative implementation or numerical inverse run is certified by this acceptance.

## Everywhere-nonsingular source Jacobian

The recovery ordering (T,R,rC,h,g,a,rD,rA,rB) genuinely makes the nine raw-moment Jacobian block lower triangular. The source sampling, clock, current-block routing and B/C ties are unchanged.

The explicit root determinant is algebraically correct and positive. The C and A rate derivatives are positive survival-exposure integrals over a nonempty positive-duration interval. The BC ratio derivative follows directly from a strictly decreasing weighted tail average; its strict negativity yields a positive two-by-two pulse determinant. The AB determinant is a strict covariance calculation: the exposure min(t,T)-a is increasing and nonconstant on (a,T), while exp(-ct) decreases. This proves a positive derivative determinant rather than inferring it from global uniqueness. The tied-B survival exposure is h plus any B-arm exposure on the stay/stay route; other routes retain exposure h. Its rate derivative is strictly negative, so the BB Laplace derivative is strictly positive. No merged descendant is assigned a fresh independent parental flag.

Each diagonal determinant remains positive when population rates coincide. The physical-to-recovery coordinate map is invertible with determinant of absolute value one; shifting all nine moments to Bernoulli means multiplies rows by 1/2. Combined with accepted global injectivity, local analytic inverses agree on the open image. This does not establish a uniform condition number on the entire positive domain or feasibility of arbitrary feature vectors.

## Joint interval-right-hand-side contractor

For any fixed rational matrix Y, the displayed Krawczyk expression encloses every x in the physical box whose F(x) belongs to the entire target interval box. The segment mean-value matrix lies in the entrywise Jacobian enclosure because the physical duration/rate/probability box is convex and remains within the strict source domain. The algebraic identity is correct without assuming Y invertible. Y=0 is a valid no-op fallback.

The full target box must be retained; replacing it by a center would change the guarantee. Jacobians must bound the whole convex physical box, not merely points satisfying narrower auxiliary constraints. Differentiating un-clipped analytic formulas is required; differentiating numerical clipping is not valid. Every other global-cover box remains retained, and whole exported-union diameter remains the accuracy quantity. No point-target existence/uniqueness test, finite-budget convergence or practical localization is imported.

## Reproduced checks and prior attribution

Control source b685db02199c7438b6d6c13a10b631803f4d32791328abbab31926fe52928217 was read and independently executed using the already available symbolic package. Result SHA256 046dd1d0beb3ff7dc495732272d1923656a76a7f2391ff9cd3e170a75d3e210a reproduces byte-for-byte. It checks the explicit root/variance, AB derivative and equal-rate identities, BC/AB determinant factorizations, B exposure, coordinate change and arbitrary-preconditioner algebra. Strict integral/covariance signs and the general inclusion rest on the hand argument, not finite controls.

Goldsztejn's primary arXiv:0811.2984 Theorem 2 and equations (6)-(7) were independently read. They support the established all-parameter interval-enclosure methodology. Krawczyk, interval Newton and interval automatic differentiation are classical; no new generic solver or historical priority is asserted. The document accurately labels the incomplete fresh access to Hansen–Sengupta's original paper.

## Next execution boundary

A separately frozen derivative/operator implementation, rational preconditioner, interval-target fixtures and conservative global-cover replay are still required. In particular, nonsingularity does not imply regularity or useful contraction of a coarse interval Jacobian. The next bounded test should measure contraction across all nine physical coordinates on the declared cover, retain two-source ambiguity, and report unresolved regions without further blind sweeps. Phased-data admission, literal feature extraction and calibrated simultaneous confidence intervals remain unfinished pipeline stages.

<!-- END ORIGINAL jacobian_review -->
