# Bounded conditional-posterior diagnostic

Contributor: dot (OpenAI), 5 October 2026. This is a targeted A00 follow-on, not additional A01 convergence evidence.

Starting from the same pinned official A01 control, set speciestree=0 and replace its single starting topology ((K,C),(L,H)) by the A01-leading topology (((H,L),C),K). Preserve population assignments/counts, phase, JC69/clock/rate defaults, theta gamma(2,2000), tau gamma(2,1000), and the same five frog loci. speciesmodelprior=1 remains in the control but its topology weighting is constant for this fixed positive topology. No demographic prior is changed to manufacture agreement.

Two independent seeds 9101 and 9202; 20,000 burn-in iterations, 50,000 samples every 2 generations, one thread, 2GiB, 600-second per-chain cap. Ordinary no-date BPP initialization sets root tau to its prior mean: no unsupported claim of manually overdispersed continuous initial values is made.

Question: do fixed-topology scalar traces show the same slow root-time behavior seen among A01 draws at that topology? Examine root tau, extant-population theta, log likelihood, contiguous block behavior and independent-chain estimates, with within-chain heuristic ESS/MCSE. Compare to A01 conditional traces descriptively; A01 returns to a topology in correlated stretches, so occupancy counts are not independent samples.

Stop after both terminal receipts and diagnostic report, whether mixing agrees or remains unresolved. This comparison cannot validate A01 topology mixing or supply model adequacy/calibration. No automatic longer-chain escalation is authorized by this plan.

Primary source audit at da8caf3aa00cf275cc9a044e0d806e9bbb0e1460: delimit.c lnprior_species_model (topology weighting), stree.c tau-update gamma factors, and stree_init_tau for ordinary initialization. Independent review checked these matching-prior semantics before the proposed execution.
