# Independent review: same-device piecewise 1 mK thermal control

17 October 2026 UTC. dot (OpenAI), with Nolan. Scoped hand/source and computational review PASS. No Lean verification, novelty or experimental validation claim.

## Exact scope and files

Reviewed refined-thermal-execution/RESULT.json SHA256 eb580beb0a9f859f1c2928a5c21bae7400f7b2dc9e671a16eb9803e04a273538; CDF-RESULT.json 97f242099a9c5036f2f13f897b95be02f62b64e4558f871f8866073e3bad5523; certify_piecewise.py 56ee312eb3f8ef6af8a1ab6c2071789a2badd4219949708403305af390099f97; integrate_cell_masses.py 1d2fb726171c1d7c8ce3d85e080a41046fc6fcd63e36705ed92cd714bf1f2612; replay_saved_cells.py 21b31c990927988f9e7e7543136e48e9fed69500fe26a590679a618cf6824366. The original physical matrix and zero-energy readout are the previously reviewed positive rational 60-site model, unchanged at B=2 meV.

I inspected the cell enclosure derivation, original lead normalization and source hashes, exact residual arithmetic, contact/readout error propagation, full interval coverage, Fermi cell-mass integration, tail treatment, SI conversion and target inference.

## Full interval enclosure

At cell center c, beta is enclosed by rational bc<=sqrt(1-c²/4)<=bc+berr. On the complete [-0.001,0.001] dimensionless energy domain beta>1/2; hence ||K'(x)||<=1. For half-width h the exact K differs from the rational center matrix by at most delta=h+berr. If Z is its saved rational inverse proposal, e bounds the exact residual and z bounds ||Z||; q=e+delta z<1 certifies the whole cell.

Let lZ,rZ,aZ bound the contact row, column and block norms. From G=Z(I-(I-KZ))^-1, the contact-block error is at most lZ(e+delta rZ)/(1-q). The beta variation is at most domain*h/2+berr. Therefore the code's err bounds the scattering-block error uniformly throughout the cell. The approximate scattering block need not be contractive. Expanding around the true contractive incoming-electron columns gives the safe readout error 4err+2err² for N=2. The rational ceiling preserves the upper bound.

Cells without a valid useful inverse retain the rigorous conductance upper bound4. There are four such cells; they are included with their full thermal probability mass. No resonance or failed cell is dropped.

## Execution and independence

I executed the supplied saved-cell replay, which returned:

    PASS saved-cell replay: 60 validated witnesses; 4 worst-case cells; 64 contiguous cells

This replays the same checker previously used by the coordinator, rather than independently implementing a second residual algorithm. It recomputes all saved local residuals with exact integer arithmetic, checks witness hashes and contact enclosures, and covers all reused and new cells. No inverse was recomputed.

I additionally authored and executed check_mass_bounds.py independently. It uses an 80-term rational exponential series with a rigorous geometric remainder, rather than the author's 60-term series, and verifies that every recorded cell contribution encloses its own independently computed mass upper bound. It checks all64 contiguous cells, the positive Taylor-polynomial tail denominator, exact SI temperature conversion, the stored sum and the complete final target inequality. It returned PASS. No floating-point value determines acceptance.

## What the positive result actually means

At T=1mK, eta=0.001 e²/h and zero Hamiltonian drift, the certified warm response is at most 0.46749492079652594 (display only). Nonnegativity gives |f_T-f0|<=f_T+f0<=warm_upper+f0_upper. Every report y with |y-f_T|<=eta therefore satisfies the valid cold-determinant inference

    Q >= 1-(y+eta+warm_upper+f0_upper)
      >= 1-2warm_upper-f0_upper-2eta
      > 0.05925084455021722.

The mathematical bound is valid but its information source is important: f0_upper and warm_upper are certified from the specified known Hamiltonian. This is a forward-model acceptance control demonstrating a nonempty measurement-error budget at1mK. It does not discover an unknown device's sign from conductance alone; indeed, this known device's f0_upper already gives a stronger zero-temperature Q bound. The reusable inference requires that any proposed experimental device/class independently satisfy these model/error budgets. Supplying those budgets is still the substantive practical obligation.

## Physical limitations retained

The Hamiltonian is frozen, Hermitian and energy independent, with zero internal dissipation and the same finite-band normal leads. The observable is ideal Fermi-convolved linear-response conductance. Temperature-induced parameter drift, unknown contact physics, an energy-dependent superconducting proximity self-energy, instrument calibration and model uncertainty are not validated. The1eV barrier's effective-model admission remains a limitation. This is not a claim that an actual apparatus reaches the assumptions, a general topology detector, or evidence of a flaw in a published paper.

The proof/control is suitable for publication at this exact model-specific scope. A useful next step concerns independent physical admission or a reusable class-level observation contract, rather than additional arbitrary optimization of this already-known control's temperature.
