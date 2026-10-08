# Prereview mapping and typed input/output contract

Authority: repaired [Python receiver](../2026-10-07-cloud-practical-signed-guard-2159z/signed_receiver.py)
and unchanged [Rust interval core](../2026-10-08-cloud-rust-interval-root-0000z/src/lib.rs).
Status: source candidate; no new receiver execution or acceptance.

| Python block | Rust counterpart / retained operation |
|---|---|
| Arithmetic27–75; Interval78–106 | Original root ReceiverContext/ReceiverInterval methods, same ordered endpoint checks/coercion/rounding/reciprocal/exp accounting. |
| rational108–117; box120–130 | Request::from_ordered_text/parse_box use core parse::receiver; low then high parse, unrounded domain check, context interval construction. |
| receive139–156 | Config before inputs, two means then two physical boxes; all mean meets, ordered mean/prior differences, separate A/T constructions. |
| Root157–171 | a0/a1/b1, rho1, ER, K, DR, JT, DT with original chained interval operation sites. |
| CC172–176 | Charged CC exponential, signed CC/AC/time residual, original derivative interval and prior meet. |
| h177–185 | Positive pulse denominators, Q1/EH, original h/T/rC/rR signed bound and prior meet. |
| g186–190 | EG with charged upstream exponential after numerator evaluation; GN, shared y0/g0 denominator and DG. |
| A/d191–200 | Both AB shared contrasts, time/rate lifts, BA/DA, Bd/DD; exact scalar absolute-bound calculations. |
| AA201–202 | Shared AA/AB/A bound and prior rA meet. |
| BB203–207 | Both charged tied-B exponentials; same BB/AB/BC/AC continuation and nuisance bounds. |
| Difference/normalization208–221 | h,u=A−h,v=T−A, five rates,g in original order; original widths and strict1/20 threshold; residual order root/root_time/h/g/AB1/AB2/BB1. |

Public inputs: Config with i32 precision/max_bits/max_exp_calls, two fixed
nine-pair text arrays in AC1,AC2,CC1,BC1,BC2,AB1,AB2,AA1,BB1 order;
two optional fixed physical arrays in h,u,v,rA,rB,rC,rAB,rR,g order.
Means begin in[0,1] then meet[1/2,1]. Original physical D:
h/u/v∈[1/32,1/8], rates∈[1/2,6],g∈[1/6,2/3]. Config uses original ranges;
raw grammar/256-bit bounds come from the frozen core receiver parser.

Public output: Outcome.geometry Result<Geometry>, scalar_exp_calls,config.
Geometry exposes exact9 interval differences,9 normalized rational bounds,
maximum and7 residual intervals. status() maps all errors to UNKNOWN and
successful geometry to conditional certification iff maximum<1/20.
prepare errors can be captured by Outcome::refused with zero exp calls.
No source existence, mean-band coverage or outer cover is inferred.

The candidate's Rust helper names differ from mathematical A/d notation.
All additions/subtractions/divisions use the core's fallible methods; plain
Rational arithmetic is used only at the Python Fraction-only scalar sites.
Native provider/provenance is a separate implementation field. File loading,
malformed Python objects/dictionaries and arbitrary invalid external
BigRational contexts are outside the sealed typed input promise.
