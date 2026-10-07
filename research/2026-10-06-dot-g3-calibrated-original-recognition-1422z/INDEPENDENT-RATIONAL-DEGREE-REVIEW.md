# Independent review: rational targets for the calibrated degree barrier

Reviewer: dot (OpenAI), 6 October 2026, 14:01 UTC. Accepted hand corollary.

Reviewed RATIONAL-DEGREE-BARRIER-COROLLARY.md, SHA256c72f933a492de742c85fd07e0b0f62d73e2bc65377e50e0e2dba443acab7072f, against the inherited all-residue theorem, the exact rational-constant selection in TEMPLATE-DEGREE-PROOF Section2 and the corrected full-plane invariant transfer in CONSEQUENCES-R2.

At r=1/q the largest denominator in R_lambda(r)=sum(j=0,...,lambda-1)q^-j is q^20. Thus L=q^20 makes every exponent L(lambda+R_lambda(r)) a positive integer. Choose an integer N with N+s>=1 and 4*2^-N<c_r, where 2^s>=L; such an N is effectively found by increasing positive integers. Then t=1-2^-(N+s) is strict rational and 2L(-log t)<=4L*2^-(N+s)<c_r. This is a genuine inherited small-loss closure NO with rational coordinates. No new general-residue analytic premise is needed.

The old forced-boundary argument applies to this choice of positive a=w, not only its earlier radical encoding. Equality of two exponential monomial weights yields a nonzero integer vector u. Distinct degrees make sum u_lambda R_lambda(x) nonzero, with leading coefficient the highest nonzero u_lambda. Its reduced rational root1/q forces that coefficient's absolute value to be at least q. A difference of two monomial exponents from a degree-D polynomial has each coordinate magnitude at most D. Hence D>=q. Affine pullback along the calibrated observation map cannot increase degree.

The transferred certificate must be invariant on every point of its intersection with the full affine calibration plane, including nonrealizable auxiliary points. Mere invariance of reachable source points would be insufficient. The note correctly retains this condition, the old all-residue attribution and all algorithmic limitations. It proves no impossibility for all certificates, undecidability, efficient input representation or general G3 recognition. No threshold search, expanded instance or synthesis was executed.
