# Independent review and exact saved-witness replay

2026-10-17 UTC. dot (OpenAI), working with Nolan. Verdict: scoped PASS.

Reviewed author certify_inverse.py SHA256 da92af01acf9cba3fcd8757aee05634f6992565c184ea5780ecee60326f64c78, RESULT.json 21c3fb460b49d07fdbfb0e1ead390ddc89a93ea5c301b903a180cf72005ca14b, and updated CERTIFICATE-EXPLANATION.md 47ea201a8de3314b8f8d4444c6a8a7871c1b52676d2fde7882d73750a137e80a. Candidate17's symbolic review remains separate.

Executed independently authored check_saved_certificate.py using only standard-library integer/Fraction arithmetic, without NumPy or a new inverse. It reconstructed all 240-by-240 K entries from the exact published positive profile and hopping convention, compared the full sparse input, checked saved artifact/source hashes, computed every entry of KZ-I, and independently reproduced both squared Frobenius sums, ceiling square roots and rational rho. The prior conductance JSON was independently fetched at immutable f174251a09468254c778a1136ed5b975173fc378 and matched local bytes exactly (SHA256 9e1eb9198562c8696d005819c6ffb8aa40d236c5afa4d3ff80d8ce3b96906647).

The inverse proposal is not trusted. For e>=||KZ-I||<1 and z>=||Z||, the finite square matrix K is invertible and ||K^-1||<=z/(1-e), proving the displayed lower singular-value bound. The checker recovered

rho = 140737488339021024616545991/2093504124813124966500000000000,

approximately 6.72257994006025e-5 in normalized energy units.

For W=rho/2, beta_W>=1/2 and d=rho/2 make candidate17's N=2 Lipschitz constant at most 4+32/rho². The exponential tail bound, full first moment bound, global 0<=f<=4 and reused exact f(0)<1/250 establish the actual ideal warm response upper bound. Adding 2eta correctly handles every reported y within eta of that response; a favorable unattested measured value is not assumed. Independent rational evaluation recovered Q_lower approximately0.9811998919259491 at eta=0.001 and T approximately5.244439280192143e-12 K, with identical frozen Hamiltonians and zero drift.

The SI conversions are exact: k_B=1.380649e-23 J/K and 1 meV=1.602176634e-22 J. These are an exact sufficient mathematical budget in the specified model, not measured apparatus performance or a useful laboratory temperature.

Also hand-checked the appended window optimization argument, including y>=0. For theta>=rho and W<rho, the kernel lies between 1/(8theta) and 1/(4theta), implying alpha<=W/(2theta) and m1/alpha>=W/4. The chosen rho-based L_W is at least8/rho². AM-GM then gives U>=4sqrt(eta theta)/rho. Independent exact arithmetic verifies theta>=rho and 16eta theta>rho² at1mK (squared lower-bound display approximately305.085), hence every larger temperature as well. This limitation concerns the particular bound built from the chosen certified rho and eta; it does not bound the true smallest singular value, actual observable regularity, or information available to better measurements/analysis.

No new interval scattering solve, finite-energy integration, experiment, original-paper replication or Lean build was executed. The 1eV endpoint-barrier model-admission limitation remains. Publication requires coordinator integration of this receipt with the author packet.

Independent checker SHA256: 7b3fbfa6cfc48010ccc9c15324e37d33f7fec28656108805049c1a1811ac3877.
Independent output SHA256: e501dc3c2481a07ab029534f5bb0ceb56281888b224f75004f254dd75af870c7.
