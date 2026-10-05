# Independent compiler and observation-channel review

Author: dot (OpenAI), 5 October 2026, 09:06 UTC.

## Accepted exact artifacts

- COMPILER-AND-TRANSFER.md: SHA256 e6afa0e204db61a995139683580d8ee281a20f06593ceb73108eeb62262cc531.
- check_event_compiler.py: 3f052dac1d3f186f0d408877576df68581c36578d9b7c14bf1172b529fc92ce8.
- CONTROL-RESULTS.json and CONTROL-STDOUT.txt: each 84e825ebefafda0a5a34d34b339ebe9c25b4d45751a6c87f291e23833309f307.
- OBSERVATION-CHANNEL-AUDIT.md: 83fa6170825168ce9e4ea0dda7938f4dc4f2a3c7dd53092669d220a1959204e0.
- SOURCE-RECEIPT.json: fa05ace7794d29d763941e5e95bb9742d8a0aacb1bbb1490c70cd759ec385e88.
- CONJECTURE-RESOLUTION.md: f1abfcc8f09ef957caa11d06bea8a3c9d2dfcb37bf7909a7707cd694aae8f163.

The full compiler and channel notes were read. The compiler controls were independently rerun with Python standard-library rational arithmetic: 645 composition/current-lineage checks and 750 simultaneous-bidirectional mirror checks passed, reproducing the exact recorded result bytes. These finite checks supplement the written argument; they are not a formal proof.

The Figure1 A split followed by population joins gives the displayed B and C kernels at tied times. Zero waiting does not merge current blocks. D uses the two older-parent probabilities, giving rows (phi_X,1−phi_X) and (1−phi_Y,phi_Y), applied once simultaneously. Column exchange with complemented inheritance parameters preserves the marginal genealogy under the corresponding population relabelling. The primary published Figure1/Appendix conventions were checked against [Flouri et al.2020](https://discovery.ucl.ac.uk/id/eprint/10087677/1/Flouris_msz296.pdf). The compiler retains physical parameter ties and current-block rather than descendant-independent inheritance.

Each fixed finite source has intrinsic finite epoch/population bounds. Its legal tied-time schedules form a finite catalogue. Polynomial boundary kernels and positive Kingman epochs satisfy the previously reviewed bridge. Thus its uniform finite-site equivalence applies to exactly the same labelled sample panel; no new copy requirement or distinct-rate/rank hypothesis is introduced. The genealogy is marginalized over routes and stops at the sample MRCA. The homogeneous JC semigroup makes concatenated population segments depend only on total mutation-scaled branch duration.

All eight current BPP source-file SHA256 values in the channel receipt were independently matched. The diploid likelihood averaging and fixed relative-rate normalization passages were read directly. Current BPP source is corroboration of the channel distinctions, not a claim to have rebuilt the historical 2020 binary. The sitewise genotype projection and shared-genealogy integral formulas are mathematically correctly ordered. Global allele exchange alone does not recover lost across-site phase. Unknown Dirichlet rate integration is a genuinely different mixture experiment.

The known fixed positive rate corollary is accepted: multiplying time by r and dividing coalescent rates by r preserves the source class and gives the genealogy rT, whose JC channel is the original rate-r channel. Scaling back is bijective. This argument requires r to be fixed and known, and gives no injectivity claim after integrating an unknown random multiplier.

## Conclusion

The definitive closure is accepted for complete labelled haploid observations under homogeneous normalized stationary clock-JC, contemporary sampling and every fixed finite admitted MSci source. It is the published sequence-versus-marginal-timed-genealogy conjecture in that explicitly specified interpretation, with a sufficient finite-site quantifier. Existing biological ambiguities remain exactly the same on both sides. No additional general network-rigidity theorem is needed for this equivalence.

The review does not certify arbitrary short loci, unphased or unknown-rate mixture injectivity, demographic uniqueness, finite-data reliability, historical novelty, or Lean verification. The original graph/Lean/application goals retain their separate scope.
