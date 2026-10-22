# Exact-real G7 formula frontend

Status: SOURCE ONLY, UNCOMPILED/UNEXECUTED. No solver/backend/model, Cargo,
native binary, CI, compiler or new worker ran. The original G1–G7 goal stays
active. This component does not return an identifying policy or budget NO.

native/g7_exact_law_formula.rs is a pure Rust library. The separate
native/g7-formula/Cargo.toml binds it to the already recovered exact
parity_solver Polynomial/Rational implementation. It declares no CLI, parser,
dispatch task, process, filesystem or network writer. The original biological
compiler, source census, QE and CAD providers are reused as separate suppliers.

## Typed input and exact scope

Problem declares one ordered original forcing-row alphabet, one finite base
observation alphabet, a finite target-labelled polynomial source-model family,
algebraic constants and finitely many semialgebraic action/support cases.
Each source model has its OWN parameter arity/domain, and exactly one shared
row-major base vector of dimension D=rows*base_observations. Model target is
constant on that piece; split a parameter-dependent finite target into pieces.
All polynomials use constants first, then source-local OR action-local symbols.

Rows have exactly r original-ID Option<Bool> slots. Sites are DERIVED from
their Some entries, including forcing to false. Duplicate forcing records
are refused as resource aliases. This does not deduplicate G6 constraint rows:
those ordered constraint/multiplier positions remain unchanged. Multiple
observation/channel modes are base coordinates or action modes, never new
physical configuration IDs. The complete menu/census/readout interpretation
is a supplier obligation, not authenticated by the typed container.

Every action supplies exact positive original-row support and a polynomial
weight for EVERY row. The generated guard requires positive weights on support,
zero elsewhere and total1. StochasticChannels adds nonnegative, mass1 channel
rows and DERIVES coefficient B[o,row,obs]=w[row]*C[row,obs,o], with offset0.
SuppliedAffine accepts a declared B/b specification and guards zero coefficients
on absent support rows. Its case IDs are exposed by supplied_affine_cases():
actual-programme correspondence is still mandatory for EACH such case.
No dictionary field or caller Boolean supplies that proof.

All actions are source independent and real valued. Fixed semialgebraic action
domains plus these exact support guards form the allowed family. Variable
output dimensions can be embedded in a common finite output carrier by zero
padding; that typed bridge remains part of supplier integration.

## Whole-history game and resource state

H excludes every pair of consistent source states with different targets.
Each source copy receives ONE parameter bank, used for its domain and EVERY
history equation. The competing source gets a distinct bank. No fresh source
parameters are allocated per row or response.

W0=H.
W(d+1)=H OR disjunction_over_cases(
  exists action_parameters,
    allowed_action AND forall exact_response, Wd(updated_history,state)).

Action variables lie outside the competing-source quantifiers and before their
future response. They may depend on the entire previous history. Invalid or
physically impossible histories are kept distinct: impossible histories satisfy
H; ReachableHistory separately asks for a whole-history consistent model.

Resources are executed calls plus unions of positive original rows/sites.
A PathBudget is a nonempty finite union of downward ResourceCeiling rectangles,
with optional allowed original row/site sets. This supports standard call/row/
site caps and arbitrary finite downsets in THESE coordinates, including
combined objectives encoded by their maximal states. It does not implement
arbitrary irreversible/value-dependent resource updates. Deletion preserves
this syntactic legality, so the general affine bound D applies. Retained depth
is min(D, affordable remaining calls), not the pooled prototype's row count k.
Different varying channels do not create extra charged original rows.

AST/input/bit/exponent/symbol/output and construction-depth limits are explicit.
The current recursive builder additionally refuses depth>128. These engineering
limits return Error::Limit, an UNKNOWN/unavailable result; they never return a
false winning formula or a losing-budget certificate. Invalid dimensions,
IDs, duplicate aliases or malformed prefixes return Error::Invalid separately.
No source-census completeness follows from either validation path.

## Backend queries and policy interface

compile(problem,budget,prefix_case_ids,emit_action_fibres,limits) returns a
Compiled value immutably borrowing BOTH complete inputs. Prefix case IDs fix
only the finite case path. Prefix actions and responses remain FREE real
symbols, exposed by history_symbols(); no transcendental response is converted
to a rational sample or global algebraic constant.

QueryKind includes ConstantsWellDefined, LegalHistory, ReachableHistory,
HomogeneousHistory, WinningContinuation and optional WinningAction fibres.
A fibre exposes free next-action coordinates and universally quantifies its
next reply and remaining game. Disabled fibres explicitly retain affordability
and enabled_in_retained_horizon; their formula is false and no action is selected.
The output is a relation for the EXISTING history-relative algebraic selector.
It is not an executable next-action oracle.

Each algebraic constant is a rational univariate polynomial plus STRICT
rational isolating interval. ConstantsWellDefined is the existence AND
uniqueness formula for the ENTIRE shared tuple. It MUST be true before any
other query is interpreted. An invalid/no-root/nonunique description is a
prerequisite failure, never a budget NO. Other decision relations universally
bind this tuple under its root constraints; without the prerequisite their
implications can be vacuous. Reachability instead existentially binds roots
and one consistent source. Root isolation/QE itself is not executed here.

wolfram_query() emits bounded Resolve[...,Reals] source for the existing
provider. All symbols/heads are generated; no caller text becomes executable
code. The iterative renderer checks each append, because DAG sharing can
expand in text. The frozen source/projection/request/result must still be
authenticated at the actual provider boundary. A Rust borrow does not
authenticate an arbitrary external dictionary, binary or origin receipt.

## Reuse and remaining integration

G7-POLICY-REUSE.md and evidence/G7-POLICY-SOURCE-INTAKE.json pin the accepted
539c G7 contract, existing census/whole-forest source solver, pooled
continuous_optimizer.wl and actual CAD selector, plus the original typed
Winning/rank/resource/strategy consumers. This library ports their game
architecture and adds general channels/free histories without replacing QE.

The original native LAW compiler supplies a bounded joint-frontier polynomial
table. Its natural G is incoming[0] probability. Original forcing can be
represented by polynomial specialization G=1 for parent0 and G=0 for parent1,
with one unchanged source bank elsewhere. This use-site still needs its
controlled-law/registry proof and coherent M0 map: G=1-physical_gamma when
incoming order is false/true. Formal specialization is NOT declaring an
interior natural gamma equal to0/1. The current native engine has no separate
forced-request field and retains its original sample/size/state caps.
Those limits cannot stand in for the all-finite G7 source supplier.

Required next links are the actual complete census/admission/source/readout
provider, effective shared polynomial rows, AST-to-Winning correctness,
verified QE with free-variable preservation, relative-history algebraic
selection and terminal target/lower-source witnesses, executable-policy
CorrectRun and frontier enumeration. General mathematical hand acceptance
is retained; this engineering component does not reclassify it as a missing
theorem or promote the prototype's execution scope.

NEW native/Cargo/Lake/CI/backend execution remains held BEFORE the first writer.
Do not invoke even Cargo metadata/configuration through an ordinary shell:
the existing authenticated Linux writer/controller/recipient/frame/sequence
and transitive hooks are still UNBOUND. No new launcher, key, owner route,
runtime task/profile/whitelist, local Git or phone artifact is introduced.
The source manifest binds the exact current library and Cargo proposal;
source review is not parse/typecheck/link/run evidence.

The first bounded original joint-LAW inlet is now source-implemented in
law_table_inlet. See G7-LAW-TABLE-INLET-CONTRACT.md. One source/model retains
ALL original forcing rows and sampling/readout menus, with literal menu
coordinate offsets. Multiple concatenated menu blocks are not one PMF and
require explicit SuppliedAffine programme maps; the constructor rejects the
single-law stochastic shorthand there. The original compiler and frozen
inputs are unchanged. Both modules remain uncompiled/unexecuted.

## Open-history result interpretation

WinningContinuation is constants-conditional(prefix_legal AND win), not bare
Winning on arbitrary free coordinates. A FALSE continuation is a losing
continuation only AFTER ConstantsWellDefined AND LegalHistory are TRUE at
those EXACT history/action values. Otherwise the false value may only reject
an illegal prefix. ReachableHistory is additionally required to call the
history an actual physical transcript. This is a mandatory backend/result
consumer guard, not supplied by an arbitrary dictionary Boolean.

A false WinningAction fibre, a disabled unaffordable case or a zero retained
horizon is not budget loss. HomogeneousHistory may already allow stopping;
a relation false at one free action assignment does not prove its fibre empty.
Use the complete scoped winning query and authenticated provider result with
all prerequisites. No backend/result consumer or executed acceptance is
implemented by this pure query emitter.
