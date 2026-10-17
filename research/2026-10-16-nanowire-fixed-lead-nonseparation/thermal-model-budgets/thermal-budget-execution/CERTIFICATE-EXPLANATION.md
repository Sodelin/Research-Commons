# A certified inverse and a deliberately conservative thermal budget

17 October 2026 UTC. dot (OpenAI), with Nolan. Executed candidate; independent review pending. This is an exact finite-instance certificate using classical residual analysis, not a new general theorem or an experimental temperature claim.

## Exact input and source recovery

The device is precisely the positive member of the reviewed rational pair at commit b6b1f91d84e58506b9028dec1ff0c59e05317224, finite-example/FINITE-PAIR-CERTIFICATE-02.md. There are 60 sites; B=2, t=501643/20000, lambda=5/2, Delta=1/5, endpoint a=1000, interior a=1234321162378001/25000000000000, all in meV. Lead and contact hopping are -tau_z meV, onsite zero, no internal dissipation. No fitting or profile change occurs.

The zero-temperature input f(0)<1/250 is checked as an exact rational comparison against the saved reviewed conductance result at f174251a09468254c778a1136ed5b975173fc378, conductance-example/CONDUCTANCE-RESULT.json. Its recovered byte hash is 9e1eb9198562c8696d005819c6ffb8aa40d236c5afa4d3ff80d8ce3b96906647. This is reused evidence, not a new rerun of that earlier interval computation.

## What the execution proves

Normalize energy by 1 meV. The 240-by-240 matrix K=-H+iPi is represented exactly by Gaussian integers divided by d=25000000000000. NumPy proposes an approximate inverse; its entries are rounded to Gaussian integers divided by s=2^48. No accuracy claim about NumPy is trusted.

The script computes every entry of d s (K Z-I) by exact integer arithmetic, exploiting only the sparsity of K. It sums the squared real and imaginary entries exactly. An integer ceiling square root gives e>=||KZ-I||_F. It likewise obtains z>=||Z||_F. The two integer-square-root inequalities and e<1 are explicitly checked. The Neumann-series theorem gives

    ||K^-1||_2 <= z/(1-e),  s_min(K) >= rho=(1-e)/z.

RESULT.json preserves the exact integer sums, ceilings and rational rho. Decimal displays are not accepting comparisons. The saved Gaussian-integer Z and sparse K permit a checker to verify the residual without NumPy or inversion.

The script also checks exact Hermiticity, the signed-permutation physical PHS identity, channel indexing in the recovered conductance source, and its strict rational conductance bound. It refuses optimized Python (-O), since assertion guards must run.

Result: rho is approximately 6.72257994006025e-5; e is approximately 1.1586802900932021e-10. This rho is a certified lower bound, not a claimed exact smallest singular value.

## Exact end-to-end sufficient budget

Use candidate17 with W=rho/2<1, no Hamiltonian drift, and the rational conservative constant

    L=4+32/rho^2,
    theta=rho^2/10000,
    p_upper=2theta/W,
    eta=1/1000.

Here theta=k_B T/(1 meV). The finite-window tail is p<=p_upper, using exp(x)>=x for x>0. The truncated first moment is at most the full first moment 2theta log 2<=2theta. The local conductance is between 0 and 4 globally in the lead band, and zero outside the band. Therefore the actual warm response satisfies

    f_T(0) <= 1/250+2L theta+4 p_upper =: w_upper.

For EVERY measurement y with |y-f_T(0)|<=eta, y+eta<=w_upper+2eta. The thermal certificate thus returns

    Q >= 1 - (w_upper+2eta+2L theta)/(1-p_upper).

All operations in this final evaluation are exact rational arithmetic, and the resulting lower bound exceeds 0.98119. This establishes a nonempty deterministic temperature/error regime without assuming a measured warm value that the device cannot attain. The measured quantity is ideal Fermi-convolved conductance; no instrument experiment was performed.

Using the exact SI constants k_B=1.380649e-23 J/K and 1 meV=1.602176634e-22 J yields T approximately 5.244439280192143e-12 K. The chosen conductance error is 0.001 e²/h. These are a sufficient budget, not optimal tolerances.

## Interpretation

The bound is mathematically nonvacuous but extremely conservative: picokelvin-scale temperature is not a useful laboratory certification regime. This calculation does not show that higher temperatures fail, nor that the actual energy response is this steep. It exposes the conservatism of a full-inverse worst-case derivative bound for this chosen near-resonant device. A sharper observable-specific or validated finite-energy calculation would require its own proof and execution. The original 1 eV endpoint-barrier effective-model validity is still unestablished; no practical device feasibility follows.

## Reproduction and provenance

Run `OPENBLAS_NUM_THREADS=1 python certify_inverse.py` with the already installed NumPy. The exact verifier arithmetic uses Python integers/Fraction/isqrt. The output matrix may depend on the numerical inverse proposal, but any accepted proposal has the stated rigorous residual proof. This is author execution; no independent replay or Lean verification is claimed yet.

The initial executed script/result/log are preserved with INITIAL labels. The operative successor adds explicit physical PHS/source checks, an optimized-mode guard, and removes an unused preliminary constant expression. Its mathematical inputs and displayed results are unchanged. Source hashes and data hashes are recorded in RESULT.json.

## Window optimization cannot rescue this bound at 1 mK (additional check)

This refers only to the preceding rho-based worst-case bound, at eta=0.001 and a nonnegative measured y. It is not a claim about the actual finite-temperature conductance or all possible certification methods.

At T>=1 mK, exact rational comparison gives theta>=rho. For every allowed 0<W<rho, the kernel on [-W,W] lies between 1/(8theta) and 1/(4theta): sech²(W/(2theta))>=sech²(1/2)>1/2. Hence alpha<=W/(2theta) and m1/alpha>=W/4. The exact candidate17 Lipschitz bound is at least 8/rho². Writing u=y+eta>=eta, its inferred upper bound obeys

    (u+L_W m1)/alpha >= 2u theta/W+2W/rho²
                             >= 4sqrt(u theta)/rho.

The last expression exceeds 1 whenever 16u theta>rho². `check_millikelvin_bound.py` checks that strict inequality using u=eta and the exact SI conversion at 1 mK, so it holds for every larger temperature and all nonnegative y with this error budget. This rules out improving this particular bound to the mK regime merely by choosing W differently. It does not exclude sharper observable-specific analysis, less conservative inverse estimates, a different error budget, or actual useful measurements.
