# Nolan's five-minute researcher demonstration

This guide is authored by the validation role; coordinator review is separate.
Run commands from the Research Commons repository root with Python 3.10+.
Choose new output directories; existing runs are preserved.

1. Explain the experiment before the result: six labelled phased copies,
   complete two-site loci sharing one genealogy, one fixed backward B-to-C
   pulse, tied rates and a homogeneous stationary clock-JC sequence law.
   The application asks which shared nine-parameter assignments remain
   compatible with supplied exact rational feature bands.
2. Run `python3 -B applications/practical-solver/run.py run --example informative`.
   Open the exported `REPORT.html`. Show all nine union widths and the
   complete retained cover. Explain that the narrow supplied arithmetic bands
   yield maximum normalized width about 0.00377; this is a numerical capability
   demonstration, not a measurement of biological accuracy.
3. Run `python3 -B applications/practical-solver/run.py run --example finite-data`.
   Explain UNKNOWN: the archived 1,024-locus bands still permit two particular
   source points separated by normalized rA=3/55, larger than 1/20. More solver
   work on those unchanged bands cannot soundly certify the requested width.
   Better statistics or independent new complete loci need their own coverage
   and observation-law justification. No universal sample requirement follows.
4. Run `python3 -B applications/practical-solver/run.py run --example unsupported`.
   Show the model-admission refusal. A marker alignment or nuclear/plastid tree
   disagreement does not automatically satisfy this observation experiment.
5. Contrast `show --example informative` with a fresh run: the former is visibly
   SAVED evidence. Run `check --run PATH_TO_FRESH_RUN` to replay its numerical
   journal separately. Export `RESULT.json`, the exact request and complete
   journal when discussing a result with a colleague.

Suggested explanation: “We preserve all remaining possibilities and check
the numerical computation separately. We can demonstrate tight arithmetic
localization, diagnose insufficient information, and refuse inputs without a
supported scientific model. General G3/G4, empirical admission and full
application correctness are still research obligations.”

If asked about Rust: it is an optional checked-cover pair diagnostic; it does
not replace or accelerate the producer. If asked about AlphaGenome: run
`python3 -B applications/practical-solver/run.py molecular` to show matched
REF/A/B/AB **deterministic mock** outputs. Human/mouse service capabilities
were separately audited in official sources; no live model prediction was
executed. The fixture is not an ancestry observation or experimental
validation. If asked whether
this is the first solver of its kind: historical novelty is unresolved;
established related tools and the inherited interval method are cited in
[the comparison](COMPARISON.md).
