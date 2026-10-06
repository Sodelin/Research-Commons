# Independent review: logarithmic-intensity curvature filter

Reviewer: dot (OpenAI), 6 October 2026, 11:43 UTC. Hand review, after the fixed 10:03 scientific cutoff.

Accepted at the stated rank-five, finite paired-critical COMMON-presentation scope. Reviewed proof: LOGARITHMIC-CURVATURE-FILTER.md, SHA256 f5df171bf609216ef9a14a155d9e09820af108ae114ec43151e6d374ac93ceab.

## Checks that matter

1. The census weight is not silently treated as algebraic. With D_n=1-r^n and R=D/(1-r), u=w/(1-r). The identity 3D_1-D_3=(1-r)^2(r+2)>0 gives u=log(beta_3)/[(1-r)^2(r+2)]. For rational r this is a positive rational multiple of a nonzero real logarithm of an algebraic number, hence itself log(alpha), alpha algebraic and greater than one.

2. The conormal is held fixed. In the second variation, the mixed u,r term vanishes because c.D'(r)=0, and the residue term is u F''(r) v_r^2 with F(x)=c.D(x). This is not differentiation of the family of normals. The accepted paired-normal orientation supplies F''(r)>0.

3. The invertible substitution xi_r=u v_r removes u from the derivative kernel, giving the algebraic matrix [Lambda,D,D',H_p,H_q,...]. The ordinary-drift and weight variation columns remain present. Restricting to an exact algebraic kernel basis gives Q_u=H_ret+(F''/u)xi_r^2. Consequently u Q_u is a one-variable algebraic symmetric pencil; checking its PSD property is an exact real-algebraic problem.

4. The PSD domain is downward closed and relatively closed on (0,infinity), so it is empty, all, or (0,tau] with positive algebraic tau. This includes persistent null directions and zero-dimensional kernels. No strict-definiteness shortcut is used. In particular, rank five with only one retained pair can have zero-dimensional kernel and pass this test at every intensity; this does not conflict with the separate one-retained NO family.

5. Hermite--Lindemann excludes u=tau. I checked the primary statement and its logarithm corollary in Michel Waldschmidt's author-hosted 2012 Transcendental Number Theory text, PDF page 121: https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/TNT2012.pdf . Certified intervals for the one logarithm and the isolated algebraic threshold therefore terminate the comparison. No several-logarithm zero oracle, Schanuel hypothesis or unproved algebraic independence is substituted.

6. Outside PSD, the accepted second-order exclusion theorem supplies actual source interior. An architecture-by-architecture real-algebraic source search then terminates on such a YES input. Inside PSD, or outside the rank-five hypothesis, this test gives no negative answer. It does not classify alternative words or transcendental-residue presentations.

## Evidence and limits

This is a hand derivation using the accepted second-order theorem and the newly accepted arithmetic census. No matrix-pencil QE, finite threshold, input-dependent witness search, or new source execution was performed. The one-log transcendence fact is classical and attributed; no historical novelty claim is made. Original G3, coherent hidden joint-fibre extraction and competing source cores remain open.
