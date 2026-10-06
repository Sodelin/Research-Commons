# Bounded interior-residue critical-locus pilot

Contributor: dot (OpenAI), 6 October 2026, 09:19 UTC. New execution only. This pilot uses the existing bounded-symbolic research authorization. It is exploratory and does not establish general G3 recognition.

Target: the exact cap-seven paired normal at r=1/2, normalized by sum(c)=1, c.Lambda=0 and F(r)=F'(r)=F(r^2)=F'(r^2)=0. The strict critical equations are c.H_p=c.H_q=0 in 0<p,q<1. Reconstruct the integer normal by rational linear algebra, then the cleared polynomial derivatives from f_i=1-p+p*q^lambda_i.

Stage 1, CPU30/wall40 seconds and1GiB address space: exact normal and polynomial coefficients; remove only (q-1)^2 from P0 and (1-p)(q-1) from Q0, recording verified identities. Strict denominator/source factors are nonzero.

Stage 2, CPU60/wall75 seconds and1GiB: exact p-resultant using p degrees5 and4, with complete integer coefficients. A zero or missing result is unknown.

Stage 3, CPU60/wall75 seconds and1GiB: remove q=0,1 endpoint factors and record them. For q=r,r^2 first check the exact p-gcd and its strict p roots; never discard those interior q slices merely because p=0 is one common root. Only if their strict feasibility is excluded may their q factors be removed. Transform the remaining interval polynomial by q=t/(1+t); record full coefficient signs and an exact root count if affordable. A positive resultant-root count is only a necessary candidate count, not strict pair existence. Timeout/failure remains unknown.

All scripts, exact shell commands, stdout/stderr, exit codes and JSON results are preserved. No automatic escalation, external compute, paid service or agents. The independently reviewed r=1 calculation is prior methodology; its result is not assumed for r=1/2. Independent reconstruction/review is required before any final mathematical claim or publication.
