# Automatic whole-policy target-leaf compilation

Current successor: executed, independent acceptance pending. The earlier v1.2
candidate and its independently reproduced symbol-capture failure are retained.

This constructor accepts an observation-dependent finite action word and derives
its terminal target guards from the source/history equations. The caller does
not supply target guards. A successful result includes a full finite policy,
source-complete real coverage checks, and a whole-policy re-verification.

For the already accepted joint affine image of the complete 546-source original
four-taxon/one-hybrid class, the genuine adaptive word is forcing0, then weights
(first-response[0],1-first-response[0]) on forcing0/1. Its six actual target
families are now constructed automatically. One original parameter vector stays
shared through both observations. No source family or graph census is expanded.

For each source model, the constructor writes ALL accumulated history equations
with symbolic earlier observations and the SAME source variables. If those
equations are jointly affine in the source parameters, it chooses a square
linear-system minor and checks that its determinant/earlier denominators are
nonzero on EVERY actual source-generated response. It never silently discards a
singular reachable cell. A completed exact QF_NRA counterexample check supplies
that source-complete rank coverage; trust is SAME_BACKEND.

The inverse parameters then give a target region consisting of the nonzero
determinant, the original open parameter domain, and EVERY residual source/history
equation. Consequently membership supplies a real original source point for the
entire history. Regions are grouped by actual target, and the entire constructed
policy is checked again for observation-only actions, real legality, PATH union
cost, reachable response coverage and correct target leaves. This second check
does not trust the inversion result as a desired output-equality premise.

Source parameters and history observations now use distinct typed SymPy Dummy
identities internally. A simultaneous capture-avoiding source renaming preserves
every original model equation; original parameter spellings are retained in the
returned provenance. Earlier observations are parsed by their public names and
mapped to separate history identities. Guard printing maps history identities
back to those public names only after checking that no source or auxiliary
identity remains. Rank/verification backend auxiliaries use fresh Z3 identities.
Legal source names such as h0_0 or action_root_0 are safely canonicalized; a name
collision never becomes a mathematical NO or a silently deleted equation.

The supplied source provider remains the independently accepted complete joint
image/surjection certificate, hash 2332f4a6e242c8a29cf9ce1e39486e4d6ce8a739b4b02d5ce87d85ce69dabcb8,
under manifest 3c11ea185f573e6bf47d62a2dde96bd6215aa8eac4073b361f3571557793cbf1.
Only the model reduction supplied by that provider is used. The borrowed policy
verifier is hash-bound in the file manifest; its generic correctness is an
implementation/review boundary, with no Lean claim.

Targets in this reduced-image control are sets of the three stable coordinate
indices. The provider's `coordinate_order` maps those indices bijectively to the
actual original-tip-labelled unrooted splits. This finite encoding retains the
complete Q set, including its original taxon labels; it is not a topology-only
scalar statistic or an anonymous-tip observer.

Install `requirements.txt`, then run:

    python3 test_leaf_compilation.py

All nine source-complete rank checks and the whole generated policy pass. Eight
negative controls retain UNKNOWN for inadequate history, repeated uninformative
rows, future-response reads, illegal normalization and nonlinear source laws.
The latter is an abstract encoding control, not an admitted biological source.
Two further controls verify explicit resource UNKNOWN at action-expression
depth64 and action-word length128. These are machine ceilings, not mathematical
stopping bounds. The borrowed verifier also retains its documented depth limits.

`test_symbol_hygiene.py` additionally checks six namespace classes: present and
future observations, action names, source/history display names and backend
auxiliary names. Every case preserves a feasible repeated-row history and rejects
the contradictory normalized history in the independent review's reproducer.
These are abstract encoding controls, not newly admitted biological examples.

`BASIC-QE-OBSTRUCTION.json` preserves the actual variable-coefficient two-step
projection that Z3 4.15.3 leaves quantified. The new affine construction does
not reinterpret this residual as False. Nonlinear projection, piecewise rank
cases not covered by one valid pivot, and automatic recursive action search stay
UNKNOWN/pending. This closes target-decoder construction for the admitted image;
it does not close the generic G7 adaptive master or prove an improved call bound.
