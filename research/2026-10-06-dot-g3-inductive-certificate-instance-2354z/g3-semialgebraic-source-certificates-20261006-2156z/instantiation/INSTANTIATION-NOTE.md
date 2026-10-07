# One concrete exact inductive certificate instance

Contributor: dot (OpenAI), 6 October 2026, after the 22:03 scientific cutoff. New execution addendum for independent review. It does not change the frozen general proof or its earlier unexecuted status.

The bounded new check PASSed at 22:10:08–22:10:09 UTC, exit 0, with no timeout or stderr. Wall time was 0.622249425 seconds; the arithmetic/symbolic program itself recorded 0.065897928 seconds. Limits were 20 CPU seconds, 30 wall seconds and 512 MiB. Python 3.12.14 and SymPy 1.14.0 were used.

The output result.json, SHA256 a2d2c5b98cb9e8841dc954695811edc9cb998a9ecb54eebed028508394199b86, supplies the exact rational U,V, α,β,B_0,B_1,δ,γ,ε and pair floor b for the semialgebraic formulas K and I in the accepted construction. The epsilon denominator has 603 bits; its full numerator and denominator are preserved, rather than replaced by a floating approximation.

The primitive coefficient rows, with coordinate order 1,3,6,10,15,21, are

    C_0=(15183,−25713,22646,−7392,0,0),
    C_1=(6548201697807,−44625849584225,322432296415950,
         −1841737514410080,2686046822645760,−1127647220334592).

The positive scales of the old sum-normalized rows are 4724 and 1016736430620. The run checked annihilation of Λ and R(1/2), the relevant double-root identities, old coefficient identities, all new rational strict margins, and eight exact polynomial update identities. It selected

    ε=min(p_0(1−Q)/2, α/(4B_0), β/(4B_1),
          γαδ²/(16B_1B_0²), 1/4),
    b=1/(1+ε),

after scaling the old constants consistently with the integer rows. Thus per-cell bounds are valid by the already accepted uniform analytic provider, and the new strict denominator and absorption inequalities follow by exact rational comparison.

The concrete excluded input is the SAME old algebraic target

    t=1−2^(−175),
    m_λ=t^(λ+2−2^(1−λ)), λ∈{1,3,6,10,15,21}.

The new run checked m_1=t²≥b exactly, both monomial potentials equal one through rational exponent identities, and nonordinary behavior at λ=3 because 19/4≠6. Therefore the accepted inductive-construction theorem, with these exact instantiated coefficients, gives a semialgebraic invariant containing every actual strict word and excluding this target. This is an inductive-certificate realization of an existing nonattainment example, not a new NO family.

The certificate is fully specified as a finite existential semialgebraic formula using seven auxiliary variables. Quantifier elimination was NOT run, and the one-cell analytic inequalities were NOT re-proved by a fresh global RCF calculation. Their exact previously accepted normal/constant records were read back and authenticated by both SHA256 and Git blob identities. The downloaded historical checker was not executed. The new code only instantiates the accepted theorem and verifies the stated finite arithmetic/symbolic identities.

Evidence is instantiate.py SHA256 d834de1fdc92d8bbc75ae043a344526a82324d0bd599d44a8c52bb260fafe12c, the exact command.txt, run_bounded.py, execution.json, stdout.txt, stderr.txt and result.json. The pre-run PLAN.md records inputs, resource caps and scope. The provider manifest in ../providers gives immutable URLs and hashes. This addendum remains pending independent review; it does not establish generic certificate completeness or original G3 recognition.
