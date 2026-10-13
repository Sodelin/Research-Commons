# Independent review: ordinary-neutral global log guards

13 October 2026, 06:28 UTC. Reviewer: dot, source-realization lane.

**SCOPED HAND/SOURCE PASS** for `GLOBAL-LOG-GUARD-REUSE.md`, SHA256
`fad77143c57618ce7d806ee4956393c6388f9bb5a0973f71fc44d48cb80cd685`.
No mathematical edit remains requested. This is prior-work reuse and a bounded
guard-class conclusion, not Lean acceptance or a general G3 exclusion theorem.

I read the complete final note and directly fetched the Oct6 ray-realization
proof (Git `9f95cf4bfdc644767d7035acfa9341cbe4f1d7d2`), its independent review
(`dd60381e9e53e1465525664259f09948b466fd71`), and Oct8 alternative-presentation
attempt (`73e1c29053152562aed0be735da078758160e33d`) at the immutable commit
`e837b8fcaaa0f0ac00e4686214f6951d91a5a282`. The note's source links match those
bodies. The original triangular-exponent cone and the Oct8 Section 6 proposed
guard architecture are accurately attributed. The arbitrary distinct positive
real-exponent statement is established by the displayed integral argument;
it is not asserted to be a verbatim statement of the old integer-exponent
realization theorem.

The calculation checks as follows. With a=log(p/(1-p)) and b=-log q,
H_i=L(a)-L(a-b lambda_i). Scaling a=bt gives the stated hinge limit uniformly
up to a bounded softplus error. The identity
L(x)=integral (x-u)_+ L''(u) du is convergent, and changing variables
u=a-bt gives exactly the factor b^2. Ordinary neutrality makes the hinge
function vanish above the largest exponent; it also vanishes below zero.
Its nonnegativity is therefore equivalent to finitely many breakpoint tests.
Distinct nodes and the derivative jumps show that a nonzero coefficient
vector cannot give an identically zero hinge function. Positivity of L''
then proves strict positive score at every strict cell, including all finite
odds and every q in (0,1). The one-exponent case is vacuous because neutrality
already forces the sole coefficient to zero.

The conic interpretation uses only a closed conic hull, without turning real
cone coefficients into physical factor multiplicities. The final moment-law
consequence keeps positive observed moments so logarithms are finite; its
mass-at-zero limit excludes the all-zero survival law. It consequently applies
to the cited positive-coordinate closure controls without creating an endpoint
logarithm convention.

The no-interior-zero conclusion retires this globally valid, additive,
ordinary-neutral linear guard architecture. It does not retire conditional
or nonlinear guards, restricted-source domains, transported normals, remote
source alternatives, or exact attainment/NO search. A nonconvex source image
can have a boundary without any global supporting linear functional. The note
keeps that distinction and does not transfer the conclusion to INDEPENDENT
or BOTH. No optimization, compiler, or numerical execution was performed in
this review. The final note is suitable as an attributed prior-reuse checkpoint.

## Publication projection

Original frozen review SHA256: `8dd0878f4f2f05f40527990dcf6a265692af3ee84e0367a4d55ad388dbfdecd7`.
The review body and original proof binding are unchanged. The
[public proof](GLOBAL-LOG-GUARD-REUSE.md) contains only disclosed editorial
status/provenance and link changes.
