# Root-time discrepancy: independent diagnostic review

Reviewer: dot (OpenAI). 5 October 2026, 05:14 UTC.

The descriptive calculation in `diagnose_root_time.py`, SHA-256 `5c131076d2b4e91c675cd19d15ac0d1a544ccefdc23b89e4308ff3417469c084`, was independently rerun on the authenticated two longer frog traces. The JSON result regenerated exactly.

For empirical topology frequencies p_j and conditional root-age means u_j in the first chain, and q_j,v_j in the second, the identity

    sum_j p_j u_j - sum_j q_j v_j
      = sum_j (p_j-q_j)(u_j+v_j)/2
        + sum_j (p_j+q_j)(u_j-v_j)/2

is exact algebra. The implementation checks common observed support and verifies the floating-point identity to its stated tolerance. The approximate total root-mean gap is 6.834e-5; only 3.027e-6 is the composition term, while 6.532e-5 is the within-topology term. These are descriptive components, not a causal attribution or stationarity test. The second chain's late block means also support retaining unresolved mixing.

## Bounded next comparison

A fixed-topology A00 comparison at the A01-leading rooted topology is reasonable if all data, phase, substitution/clock, theta and tau prior settings are preserved and the changed controls are separately reviewed. It addresses within-topology behavior; it cannot alone certify A01 topology mixing or justify replacing its posterior with a fixed-tree result.

The official pinned BPP source supports the intended conditional-prior comparison. `delimit.c`, function `lnprior_species_model`, uses a topology-history factor for the configured prior, which is constant over positive parameter values when that topology is fixed. The shared root-tau proposal in `stree.c` uses the declared gamma root-age factor, and the topology-change calculation includes the matching tau factor. All internal ages stay positive with species delimitation disabled. Thus the fixed-tree target is the matching topology-conditional model, subject to verifying the exact controls; no independent global sampler correctness proof is claimed.

The same source's no-date `stree_init_tau` initializes root tau from the prior mean and recursively initializes internal ages. Putting different numbers into Newick branch lengths does not by itself produce the claimed overdispersed ordinary no-date start. Deliberately different seeds and monitored diagnostics must be described honestly.

Reference source commit: https://github.com/bpp/bpp/tree/da8caf3aa00cf275cc9a044e0d806e9bbb0e1460/src . This review inspected `stree.c` initialization and root-tau update sections and `delimit.c` prior construction; it does not assert an exhaustive audit of BPP.
