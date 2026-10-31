# Prior-work comparison: Durden and Sullivant

## Source and scope of this check

Chris Durden and Seth Sullivant, [*Identifiability of phylogenetic parameters from k-mer data under the coalescent*, arXiv:1705.06993v1](https://arxiv.org/pdf/1705.06993v1), were identified by the retained two-site proof as a predecessor to its root-pair step. On 31 October 2026 UTC, this pass read the arXiv PDF's extracted text for §2, equation (2), §5/Theorem 5.1 and the §6 discussion. The arXiv record identifies v1 as submitted 19 May 2017. The PDF page-render requests returned no inspectable image payload through this interface; the equations below are based on extracted text, not an independent visual check. No original PDF bytes were saved or hashed.

The [publisher's record](https://link.springer.com/article/10.1007/s11538-018-0399-1) also identifies the journal article in *Bulletin of Mathematical Biology* 81, 431–451 (2019), DOI `10.1007/s11538-018-0399-1`, with a 1 February 2018 online version-of-record date. Only that record and abstract were read; the published article body was not compared with the preprint. The extracted preprint title page separately displays `September 24, 2018` even though its arXiv watermark and submission history identify v1 with 19 May 2017. The cause of this discrepancy and the exact original PDF bytes are not established. No version identity or chronology is inferred from the title-page date.

Theorem 5.1 states injectivity for the two-parameter map formed from expected k-mer distances at distinct positive k-mer lengths. Its paper uses a tree/coalescent setting with a shared population-size parameter in its tree construction. This is a prior identification result, not by itself a proof of the manuscript's nine-parameter pulse-family result. The paper's observations are expected k-mer-count distances; the manuscript uses literal phased-site character products. Neither observable is relabelled as the other.

## Root-pair connection for lengths one and two

The following is an algebraic comparison of the paper's equation (2) with the retained proof's root-only pair formulas; it is not an independent proof audit of either theorem. For a fixed known sequence length `m >= 2`, let the paper's transformed divergence parameter be `x`, its positive coalescent parameter be `theta`, and set `c=8/3`. Write

\[
u_h=\frac{x^h}{1+c h\theta},\qquad
z_k=1-\frac{f_k}{2(m-k+1)}.
\]

Expanding equation (2) for `k=1,2` gives

\[
z_1=\frac{1+3u_1}{4},\qquad
z_2=\frac{1+6u_1+9u_2}{16}.
\]

The transformations can therefore be reversed: `u1=(4 z1-1)/3` and `u2=(16 z2-1-6 u1)/9`. Under the identification `x=beta` and `theta=1/R`, they become

\[
u_1=\frac{\beta R}{R+c},\qquad
u_2=\frac{\beta^2 R}{R+2c},
\]

the root-pair moment expressions in the retained identification proof, with `beta=exp(-c T)`. Thus, on these stated conventions, the pair of expected distances and the pair of root moments contain the same two algebraic coordinates. The paper's boundary `x=1` is broader than the manuscript's strict positive-time source domain.

## Time and rate conventions for this pair

The extracted preprint's §2 defines its species divergence `t` as the **sum** of the two species-tree paths, and its sequence divergence as `t+2s`, where `s` is an ancestral coalescence wait with rate `1/N`. Its JC generator has diagonal `-mu` and off-diagonal `mu/3`. It then measures time in substitutions and sets `theta=N*mu`, so the ancestral coalescence rate in those units is `1/theta`. These statements are from PDF pages 5 and 7–8, counting from the first PDF page.

For the manuscript's contemporaneous AC pair, let `T=t0` be the root age in its mutation-scaled time and `R=rR` the root pair-merger rate in those units. Under the retained AC pair marginal, the two species paths each have duration `T` and the post-root wait has rate `R`. The preprint's substitution-scaled species-path sum is therefore `t_paper=2T`, and its ancestral parameter is `theta=1/R`. Consequently `x=exp(-4 t_paper/3)=exp(-8T/3)=beta`, while `t_paper+2s=2(T+s)` in the same units. This explains both factors of two in the root-pair formula; `N` is the paper's own inverse-coalescence-rate convention, not an assumed conversion to a diploid census size.

This is a comparison of the stated two-lineage marginal and JC normalization. It relies on the manuscript's retained AC pair marginal rather than independently deriving it from the full six-sample pulse process. It does not identify the different observables or prove that all the models, sampled data or joint laws coincide.

## Remaining work

The paper supports the retained proof's attribution of a two-length root-pair predecessor. Its theorem does not settle the subsequent B/C pulse or AB-onset assembly, establish applicability to the manuscript's biological data, or resolve overall historical priority. A visual equation check, preprint title-date discrepancy, comparison with the journal body, wider prior-work search and independent scientific review remain open. Three exact rational arithmetic spot checks of the displayed substitution passed in the earlier pass, including one boundary value `x=1` outside the manuscript's strict domain; these checks are not a proof of either theorem. No Lean, solver, proof-control, biological or source-provider execution was performed.
