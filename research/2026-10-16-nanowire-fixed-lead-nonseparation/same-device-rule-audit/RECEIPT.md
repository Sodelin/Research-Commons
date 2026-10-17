# Exact consistency check of the two saved model controls

17 October 2026, 02:03 UTC. dot (OpenAI), working with Nolan.

PASS: an executed Python Fraction calculation verifies both sharp N=2 inequalities using the full rational endpoints of the existing certified intervals. This is a derived check of existing declared-model controls, not a new scattering-solver run, ML evaluation, experimental test or inverse-identification theorem.

## Result

Displayed decimals below are summaries only; accepting comparisons use exact fractions saved in SAVED-PAIR-RULE-AUDIT.json.

- Minus device: g about 1.2092764734306582; Q about -0.2029929452424592. Lower bound on Q+g-1 about 0.006283528188199118; lower bound on Q-g+3 about 1.5877305813268825.
- Plus device: g about 0.003759313856730896; Q about 0.9962602318321561. Lower bound on Q+g-1 about 0.000019545688886918565; lower bound on Q-g+3 about 3.992500917975425.

The smallest of the four certified slacks is the plus-device low-edge slack. In particular the coarse bounds Q>0.996 and g>0.003 would not have sufficed for this acceptance; the full intervals do.

The plus device has g upper endpoint below one, so conductance alone certifies its positive determinant. The minus device's scalar conductance permits either sign in the abstract matrix region. Its negative sign comes from the previously certified full-model calculation, not from this scalar conductance inverse.

## Matched source and precision

Both packets use the same exact 60-site model, B=2, t=501643/20000, lambda=5/2, Delta=1/5, end onsite M=1000, interior a_base=1234318662378001/25000000000000 and offsets 1/100000000 (minus), 1/10000 (plus). The decimal rationals in verify_finite_pair.py equal these fractions exactly. They use the same zero-energy leads/contact self-energy -i I, r=I-2i G_LL, no internal dissipation, and two electron channels. Local conductance sums incoming electron columns 0,2 and reflected electron/hole rows 0,2 / 1,3. This is the zero-temperature grounded-superconductor readout contract.

Original interval precision is 1024 bits; stored rational endpoints are used without rounding in the post-check. The scripts and prior JSON records were read, and their model constants matched; the original full matrix computations were not repeated.

Input SHA256:
- conductance-certificate/CONDUCTANCE-RESULT.json: 9e1eb9198562c8696d005819c6ffb8aa40d236c5afa4d3ff80d8ce3b96906647
- finite-m-certificate/FINITE-PAIR-RESULT.json: 58c8eaad766a54306bff6a3b5a47d09e4f21f4be6453187b8a2201aefeee38cc
- conductance checker: a40564c64789e8472b783d3071d33f1aaf1d607c4a943f6358c32529b09e5ba1, matching its saved record.
- finite pair checker: e13592ddd3d1e17c67aa28e1d9d4a31c8f4c1edc23fce8b87647342f1415ef78, matching its saved record.

New execution: python check_saved_pair.py; completed with exit0 and PASS. Script SHA256 ab8476b12dc43075f0e8b766ad63eacefeae874580e0a30385259c0474e49c92. Output SHA256 8947f8f42734b35bd461e8aa7000b7617ad613da16eafd85e53f325004b56277.

## Public paper audit availability

Taylor/Pan/Das Sarma 2512.13825v2 Appendix I explicitly says code is available from authors upon reasonable request: https://arxiv.org/html/2512.13825v2 . The inspected Avoiding Dilution PDF https://arxiv.org/pdf/2607.14949 had no availability/GitHub match; this is not a claim that no dataset exists elsewhere.

MEDA does supply an explicit public code locator in its introduction: https://doi.org/10.5281/zenodo.21478601 , from https://arxiv.org/html/2607.26208v2 . Archive contents, dataset fields and paired g0/Q availability were not verified in this bounded review. MEDA's output PDI also differs from Q; code availability alone does not justify applying our bound to that label.

Thus the executed result is an immediate two-control mathematical demonstration. A paper-level test still needs accessible paired same-device zero-energy local g and reflection determinant with exact contact/mode conventions, plus actual predictions if auditing a learned model. No empirical failure or improvement has been established.
