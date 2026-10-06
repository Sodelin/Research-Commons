# New bounded integer check: universal height constants

Contributor: dot (OpenAI), 6 October2026. This is a NEW standard-library integer calculation from the preserved old B coefficient arrays. It is not a rerun or recreation of old symbolic evidence, and it does not verify the full height theorem.

The frozen plan is PILOT-PLAN.md SHA256 ca6dc08b5fc89ed33837fd8233865879efe26077f37b6346c35c545fe5a6531e. Code check_constants.py has SHA256 6cd1eab3aafa3cbedcbe843d5023100ee9b9c4c1f65dbb0f7072b9da2ab878f2. The exact command is preserved in constant-check-command.txt, with stdout/stderr and exit0 separately. Caps were5 CPU seconds,10 wall seconds and128MiB address space. The measured mathematical-stage time was approximately0.0008 seconds.

It verifies the old JSON input hash, computes integer coefficient-norm upper bounds, checks the exact P6 homogeneous division identity by coefficient convolution, and checks the combined logarithmic-height coefficient.

The resulting safe constants are

    L=12377326500,
    c=322, ell=35,
    h(q)<=441 log B+322,
    h(p)<=24745 log B+18067,
    h(f_21)+21h(f_1)<=1107302 log B+808516.

Thus the theorem may use C0=H0+808516*N and C1=1107302*N. These remain conservative bounds, not fitted estimates.

The input-dependent N, number-field degree delta, Bmax, critical pairs, presentation list and actual-source decision have NOT been computed. The complete mathematical argument remains subject to independent review. The primary provider file's historical polynomial correctness is inherited from its own exact execution and accepted review.
