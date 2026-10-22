# Fixed-calendar correlated positive-power receiver

The complete3602B G7FixedCalendarPowerDomain.lean body has SHA256
b9fabd9e48c66f5e8a53ac43284f51c286c925147a66411dd6693dedd07e0892.
Actual hosted Lean4.35.0/mathlib56a005 accepted all six selected complete
types/axiom audits with zero errors and zero warnings. The exact appended
submission SHA256 is
f317fdd8f247d23504cdc8dd3670b7bc758aed6d0265f569852ede815faa3491.
Every selected declaration uses only propext, Classical.choice and Quot.sound.
Complete explicit types, versions and client identities are in
[CHECKED-FOLLOWONS.json](CHECKED-FOLLOWONS.json).

In namespace Astra.FixedCalendarPowerDomain, rate is -log(x)/D. rate_pos and
rate_survival construct a positive physical rate from0<x<1,D>0 and recover
the whole-edge survival. positive_power_iff_exp states literally:

    0<x, 0<z, D>0, p q:Nat, q>0, (q:Real)*d=(p:Real)*D
    implies z^q=x^p iff z=exp(-(rate x D)*d).

correlated_slots_exists_unique takes arbitrary types Pop and Slot, one X and
positive duration per population, positive elapsed time per slot, and all
the above exact integer-time relations. It proves existence and uniqueness
of ONE Z:Slot->Pop->Real with every coordinate in(0,1) and every power
equation. No finite or nonempty typeclass is required. An ancestral unit-time
survival is represented with duration1; its X_A remains variable. Natural
inheritance is a separate unchanged bank, outside transition forcing.

This is a generic mathematical component. Rust remains uncompiled/unexecuted;
parser/rational reduction/exponent/substitution and native coefficient
refinement remain open. Original admitted-source/target/action coverage,
raw completion/readout, AST/QE/selector and runtime origin are separate.
The source-only prepared native context is not pinned import/object acceptance.
No Lake/Cargo/native invocation or change to its first-writer hold occurred.

The source review in
[G7-CONTROLLED-WORD-RECEIVER-JOIN.md](G7-CONTROLLED-WORD-RECEIVER-JOIN.md)
also records the duplicate-mask restriction of the Rust row binder. Distinct
original row IDs/resources require explicit coverage or a proved transport.
