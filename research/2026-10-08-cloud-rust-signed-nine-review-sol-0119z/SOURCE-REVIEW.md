# Independent source correspondence review

Reviewer/publisher: Cloud / Sol source backend. Review target is the unchanged [candidate library](../2026-10-08-cloud-rust-signed-nine-0008z/src/lib.rs) at immutable `a977bf11442d8edab91a220bdb73e3d4aefbd5f1` / SHA `281942b869db93c77df8b66ffcfb0a9262a93b866b78bb02011d35da53e4a13f`. **SOURCE/API ACCEPT for the sealed typed input interface; compilation and numerical compatibility UNEXECUTED.** This is independent inspection of another contributor's source, not a formal proof or a reviewer's execution result.

The review read all 174 candidate library lines, the full 220-line [signed Python receiver](../2026-10-07-cloud-practical-signed-guard-2159z/signed_receiver.py), the full [forward provider](../2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py), and the actual receiver/forward/parser APIs in the pinned [Rust interval core](../2026-10-08-cloud-rust-interval-root-0000z/src/lib.rs). All candidate files and dependency/reference identities were authenticated against immutable candidate Git objects and local bytes; the complete mapping is [REVIEW-PINS.json](REVIEW-PINS.json). No source changes, compiler, harness, native binary, API, benchmark or child agent was used.

## Input, context and refusal correspondence

Config defaults match `(precision,max_bits,max_exp_calls)=(96,4096,24)`. The actual core checks PRECISION `64..128`, then BIT_BUDGET `256..16384`, then EXP_BUDGET `0..32` before text parsing. Fixed arrays are ordered `AC1,AC2,CC1,BC1,BC2,AB1,AB2,AA1,BB1` and `h,u,v,rA,rB,rC,rAB,rR,g`. Rust parses means0, means1, physical0, physical1, each low before high; unrounded input-domain validation precedes interval construction. Its parser retains raw text limit158 Unicode characters, ASCII integer/n-over-d grammar with at most78 digits per numerator/denominator, positive-denominator refusal before unreduced256-bit checks, and rational reduction only afterward.

Both optional physical boxes independently default to original D: `h,u,v∈[1/32,1/8]`, five rates `∈[1/2,6]`, `g∈[1/6,2/3]`. This is a port of the original global domain, not a new prior. Means start in `[0,1]`, then are met with `[1/2,1]` in the same two-array/feature order. Mean differences and physical prior differences are `0−1`. A=`h+u` and T=`h+u+v` are reconstructed separately, preserving Python's interval operation sites.

The private Request fields and sole ordered-text constructor prevent injection of unrelated contexts or unchecked BigRationals into an admitted request. The cloned Rc context shares identity and the exponential counter; evaluating the consumed request retains that shared counter after success or refusal. Preparation invokes no exponential, so the documented preparation-error wrapper with zero calls is correct. Config's i32 fields and fixed string arrays deliberately exclude noninteger Python objects, dictionary/key/endpoint-shape errors and arbitrarily large configuration integers; those are outside this typed contract. Python file-loading/symlink/source-identity/OSError behavior is not a native runtime-authentication promise.

## Exact operation sites

The core checks empty intervals first, then reduced endpoint bit sizes, then outward signed dyadic rounding on every receiver construction. Scalar point coercions are rounded too. Subtraction constructs the negated right interval before addition; interval division separately constructs/checks/rounds the reciprocal, then multiplies. Four-product extrema, meets and reflected scalar subtraction/division match the Python sites. Candidate operations call those methods rather than replacing them with algebraically simplified exact endpoints.

| Python signed reference | Candidate lines | Checked correspondence |
|---|---|---|
| 147–155 | 97–109 | Mean meets/differences/prior; separate A/T; `c=8/3`, a0/a1/b1 and the scalar2/subtract1 sites. |
| 156–164 | 110–121 | ROOT_DENOMINATOR; rho1; signed ER; K clipped `[0,851]`; DR and JT/DT with the same priors and coefficient intervals. |
| 165–168 | 122–125 | Charged `exp(rC1*T0)`; CC residual; `[-48/29,48/29]` time coefficient and `[3/377,3/16]` divisor; prior rC meet. |
| 169–176 | 126–133 | y0/y1 positivity gate, Q1/EH; T/rC/rR signed nuisance intervals; `[4/9,208/51]` divisor and h prior meet. |
| 177–181 | 134–143 | EG numerator/exp evaluation order; GN; shared y0/g0 denominator met with `[1/275,1]`; signed DG and g prior. |
| 182–190 | 144–156 | AB1/2 shared contrasts; exact `(44/19,48/361)` and `(88/35,96/1225)` lifts; BA=`5*2^14*3^6`, DA, Bd=`4608`, DD with original A/rAB meets. |
| 191–196 | 157–165 | AA coefficient135 and nuisance coefficients3,7/4; both tied-B exponentials; BB residual and coefficient240 with20/11,128/57,11/8 terms. |
| 197–210 | 166–173 | Nine differences h,u,v,rA,rB,rC,rAB,rR,g; original domain-width normalization and strict maximum `<1/20`; seven residuals root,root_time,h,g,AB1,AB2,BB1. |

Several order-sensitive sites deserve explicit treatment. Python's K denominator computes the scalar Fraction `c*c` before the interval sum; that scalar computation cannot refuse under a receiver budget. Its subsequent reflected multiplication is implemented as the interval sum multiplied by a coerced/rounded scalar point. Rust's `sum.mul_scalar(c*c)` performs the same coercion and receiver multiplication before either a0 factor, so moving the harmless exact scalar calculation introduces no rounding or refusal change. The JT reflected `c/R0` followed by `1+...` maps to `scalar_div(c,R0).add_scalar(1)`, preserving both scalar point sites and reciprocal construction. Integer scalar2 multiplications, despite being exact values, still use the same coercion sites.

The EG implementation evaluates `(1-g1)*dmAC1` and `g1*dmCC1` before the charged `exp(rC0*h0)`, then divides/subtracts in the Python order. Both BB exponentials are evaluated before EB's three sequential subtraction terms. The candidate does not cancel shared contrasts, merge A/T constructions or redistribute subtraction/multiplication in ways that change interval enclosures. BA/Bd/AA/BB absolute-bound scalar calculations remain plain exact Rational arithmetic until the original interval-construction/check sites. Their coefficients fit the actual i64 integer constructor and do not introduce a machine-integer overflow.

## Scalar exponential and call budget

The actual core forward primitive matches the frozen c848 provider: domain/precision checks before zero/large shortcuts; halve to u≤1; q=`bits+m+4`; alternating series at most512 terms; width stop `2^-q`; dyadic/unit rounding after the series and every squaring; final width refusal. No hidden256/2048-bit cap is applied inside that scalar primitive. Receiver bit checks and the raw input parser cap remain distinct. Missing memoization affects performance only; accounting charges every interval exponential by two before either endpoint call.

Receiver `exp_neg` checks context then negative lower endpoint, then available two-call budget; increments by2; evaluates the upper input endpoint first for the lower result endpoint and the lower input endpoint second for the upper result; uses scalar precision `receiver_precision+4`, then reconstructs a receiver interval. Its original failure ordering is retained. The complete downstream path has four interval exponential sites and eight scalar charges: CC(rC1*T0), EG(rC0*h0), BB(rB1*A0), BB(rB1*h0). Earlier arithmetic/denominator/empty-meet or call-budget failures can stop before those charges, and Outcome retains the actual shared count. The budget must not be inferred solely from a success status.

Actual imported type/method names and signatures are present in the pinned core. Ownership, fixed array conversion, arithmetic constructor types, context cloning and two sequential E-vector removals are coherent by source inspection. There is no definite static API defect identified; that does not substitute for compiling the candidate.

## Verdict and missing implication

The source supports the intended bounded typed port of the original signed receiver. Geometry reports conditional pair widths, not the source model's computed forward means, all330 features or an inverse search. The full forward provider was inspected to confirm that those separate routines and scientific claims have not been ported or silently inferred by this receiver.

The exact missing implementation implication is a preserved transport/probe and actual compiled candidate whose endpoint arrays, all nine normalized bounds, maximum, all seven residuals, refusal strings and scalar-call counts are compared with one authenticated Python reference buffer across suitable valid/boundary/budget fixtures. No such candidate execution happened in this review. The interval core's inherited owner-reported3048-case acceptance is not a downstream receiver numerical test.

Outcome has no current scientific admission fields. A later transport must set `data_confidence_certificate_issued=false`, `outer_cover_validated=false`, `actual_source_forward_evaluations=0`, `observation_rows_replayed=0`, `mean_band_coverage_admitted=false` and `compatible_source_existence_verified=false`. Native provenance must identify the actual Rust source/binary and must not copy Python's `compile_exec_verified_single_read_bytes` execution assertion. A manually constructed public Outcome/Geometry is not an admitted Request evaluation.

Even if future finite comparisons pass, source existence, actual observation replay, mean-band coverage, useful all-nine inference, calibrated confidence, universal full accuracy and complete outer cover remain open. The strict conditional status does not discharge any of them. Root owns the later execution stage; this reviewer returns after preserving the source gate.
