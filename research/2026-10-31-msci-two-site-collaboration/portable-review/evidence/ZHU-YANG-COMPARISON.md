# Prior-work comparison: Zhu and Yang

## Source and scope

Tianqi Zhu and Ziheng Yang, [*Complexity of the simplest species tree problem*](https://doi.org/10.1093/molbev/msab009), *Molecular Biology and Evolution* 38(9), 3993–4009 (2021), is named in the retained two-site proof. On 31 October 2026 UTC, this pass read selected publisher-hosted text: “Multispecies Coalescent in the Case of Three Species,” “Numerical Comparison of Different Methods,” and the discussion of information lost by pooling sites. The authors' [UCL-hosted paper](https://discovery.ucl.ac.uk/10118758/1/2021ZhuYangMBE-Speciestree3s.pdf) also contains the selected `n=2` statement. The two sources were not compared byte-for-byte; no complete article/PDF bytes were saved or hashed.

## What the paper states

The paper studies three species with one sequence per species per locus under a JC mutation model and molecular clock. For each candidate species tree it describes four parameters: two divergence times and two ancestral population sizes. In its numerical-comparison section, it reports that full-likelihood maximum likelihood with **two sites per locus** can identify and consistently estimate all four parameters in its model. The paper uses `n` for sites per locus and `m` for the number of loci; its discussion treats the loci as independent under the model and identifies `m`, not `n`, as the statistical sample size.

The same paper distinguishes that full-likelihood analysis from pooled-site methods. In the unequal-population case its pooled independent-sites likelihood has only three independent site-pattern proportions for four parameters. Under an additional population-size equality assumption, it instead discusses a three-parameter model. These distinctions matter when describing the reported two-site result: the paper does not say that every summary method recovers the four parameters.

## Relation to this manuscript

The retained identification proof accurately names a two-site, four-parameter result in a different three-species/three-sequence setting. Our manuscript instead fixes a directed pulse family, uses two labelled samples per species and states identification through nine specified character means. The earlier paper's report does not by itself prove that pulse-family statement or establish a useful number of loci for it.

This pass confirms the cited paper's stated model and its report, not an independent proof of its global identifiability claim. The `n=2` statement appears in the paper's numerical-comparison section; this pass did not locate and independently review a separate complete proof or inspect the supplementary material. That limitation does not establish that no such proof exists. The broader prior-art search, biological applicability, author/rights decisions and the manuscript's complete Lean proof remain open.
