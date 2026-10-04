# History-dependent algebraic action sections

The finite-policy verifier now supports polynomial action sections whose
coefficients and isolating interval read only earlier observed responses and
earlier uniquely derived action coordinates. This addresses part of the inherited
real/algebraic selector encoding gap. General CAD extraction remains pending.

At each section, the verifier checks that all coefficient/bound expressions are
defined, that the lower bound is smaller than the upper bound, and that the
polynomial endpoint values have strictly opposite signs on EVERY reachable
source/history point. Polynomial continuity and the intermediate-value theorem
give existence. A separate exact two-root counterexample check proves uniqueness
in that interval. The unique root is then added to the source/path constraints,
and every later action, response, coverage and target obligation is checked for
all feasible root values along the SAME original source assignment.

Because the coefficients/bounds are functions of lawful history only, uniqueness
gives a deterministic observation-dependent selector. No hidden source parameter
or future response may enter the section. Roots do not become freely resampled
private randomness. Later own-action coordinates are known deterministic history
functions. The proof rule uses elementary polynomial continuity/IVT plus
completed Z3 QF_NRA checks, with SAME_BACKEND trust and no Lean claim.

The concrete control uses the SAME accepted nine joint source images as before,
with no graph census expansion. Force0 first, then let w be the unique root of
w^2=first-response[0] in (0,1) and use weights (w,1-w). All 180 whole-policy
obligations pass, including 18 availability/uniqueness checks. The real policy
has PATH [2,2,1] and preserves full reachable source/history coverage. The split
coordinate encoding retains original-tip labels through the unchanged provider.

`section_point.py` evaluates a supported section exactly from rational observed
coordinates and returns the accepted algebraic polynomial/root-index codec.
It accepts arbitrary polynomial degree, subject to computational resources. Its
present coefficients/bounds must evaluate to rationals; general algebraic-
coefficient lifting returns UNKNOWN. This point codec is not a complete end-to-
end algebraic response controller, and the symbolic real-policy verifier does
not imply empirical admission.

The nonnegative-power parser explicitly interprets exponent zero as the
polynomial constant1, including a zero base. This avoids relying on Z3's
underspecified total-power operation for 0^0. Earlier accepted numerical/source
examples are unchanged; the normalization is a small separately recorded fix.

Install `requirements.txt` and run:

    python3 test_algebraic_policy.py
    python3 execute_source_algebraic.py

The second command runs two original source-admitted calls under one graph and
one pre-existing positive edge/gamma assignment, in each fixed COMMON/I mode.
It chooses the algebraic weight solely from the first observed coordinate,
encodes and decodes every later algebraic response exactly, recompiles BOTH
actual history rows under that SAME assignment, and returns the actual target
by the second observed vector's minimum. Changed root/probability controls fail.
This passes one inspectable whole-source algebraic execution, not a claim that
all algebraic response/section functions are implemented by the general CLI.

Invalid root availability, nonunique intervals, hidden/future coefficients and
unsupported numeric encodings fail closed. The source-image provider remains
hash2332f4a6e242c8a29cf9ce1e39486e4d6ce8a739b4b02d5ce87d85ce69dabcb8,
under accepted manifest3c11ea185f573e6bf47d62a2dde96bd6215aa8eac4073b361f3571557793cbf1.
This is an implementation extension of existing G7, not new mathematics, a
general recursive synthesis completion, an optimal policy, or global graph
recognition/unknown-size termination.
