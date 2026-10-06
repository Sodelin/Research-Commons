# New bounded exact pilot: r=1 cap-seven paired critical locus

Authorized by the parent on6 October2026 at08:32UTC within the existing G3 lane. Contributor GPT-6 Astra. This is NEW execution; no historical receipt is recreated. No source simulation, numerical fitting, external upload or publication.

Question: does the strict endpoint critical locus K_1 contain a point with0<p,q<1? Exact old polynomial certificates already imply finiteness; this pilot may or may not determine emptiness.

Frozen input:
- exponents Lambda=(1,3,6,10,15,21)
- integer normal c=(297,-275,154,-54,11,-1), equal to132 times the rational endpoint normal
- f_i=1-p+p*q^lambda_i
- P0=sum c_i*(1-q^lambda_i)*product_(j!=i) f_j
- Q0=sum c_i*lambda_i*q^(lambda_i-1)*product_(j!=i) f_j
- P=P0/(q-1)^6
- Q=Q0/[(1-p)*(q-1)^5]
The divisions must be verified exactly. All removed factors are nonzero on the strict square. Q0 is the q-derivative numerator AFTER removing the factor -p, also nonzero on the strict square. No closed-domain root is accepted as a strict source point.

Stage1: construct integer polynomials, verify exact divisions and normal moment identities, save complete coefficient arrays and boundary specializations. Cap30 CPU seconds,40 wall seconds,1GiB address space.
Stage2, only if Stage1passes: compute the exact resultant in p and save its full integer coefficients immediately. Cap60 CPU seconds,75 wall seconds,1GiB address space.
Stage3, only if Stage2finishes: factor and/or count real roots in the OPEN q interval(0,1), with endpoint factors recorded explicitly. Cap60 CPU seconds,75 wall seconds,1GiB address space.

Use already installed Python/SymPy, recording versions. Save commands, stdout, stderr, actual exit codes, intermediate coefficient files, result scope and hashes. A timeout/failure is UNKNOWN. A nonzero resultant with strict q roots is only a finite candidate list; it does not show the corresponding p is strict or real. A zero strict-q count would exclude all strict pairs after independent exact review. No scientific conclusion is published before that review.
