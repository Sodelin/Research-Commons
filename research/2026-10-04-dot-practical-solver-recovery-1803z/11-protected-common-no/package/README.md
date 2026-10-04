# Exact common-source NO certificates without a hidden-size bound

The solver can now reject a declared COMMON source model of ANY finite hidden
size when matched natural/forcing0/forcing1 law profiles cannot share one
strict-interior original-site parameter. This is a necessary source identity,
not a complete recognizer or a new mathematical theorem.

`SOURCE-THEOREM.md` states the precise original-bit independence, sampling,
intervention, original-ID and same-parameter hypotheses. They are essential.
The polynomial minor test acts on the JOINT response vector across all supplied
profiles; profiles cannot independently refit their gamma parameters.

`common_global_no.py` performs exact rational arithmetic and emits a nonzero
minor, equal-forced-row contradiction or strict-gamma violation certificate.
`verify_common_certificate.py` independently reconstructs the input vectors and
replays that witness, including the exact input/source/site binding. Neither
program performs graph enumeration, word-bound search or backend QE.

Run:

    python3 test_common_global_no.py
    python3 common_global_no.py example-no.json --output certificate.json
    python3 verify_common_certificate.py example-no.json certificate.json

The controls include noncollinear law profiles, a strict-positive parameter
boundary, identical forced rows, and two panels that individually fit different
gammas but cannot share the SAME source. A passing necessary test returns
UNKNOWN rather than SAT. A COMMON/INDEPENDENT union returns UNKNOWN when only its
COMMON component is excluded. DNA, frequencies, nonempty empirical metadata and
shape truncation fail closed. A tampered exact minor is rejected.

Inputs are caller-declared exact unranked genealogy event-law coordinates.
This interface is not an empirical-admission validator or a biological fit.
No full unknown-size G3/G4 stopping theorem, general synthesis, novelty or Lean
verification is claimed. The rule preserves all previously accepted source
assumptions; it does not substitute a numerical catalogue for global coverage.
