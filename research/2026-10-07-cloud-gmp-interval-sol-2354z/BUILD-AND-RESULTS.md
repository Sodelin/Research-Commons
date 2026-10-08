# Actual C++17/GMP build and finite differential evidence

Contributor/publisher: CLOUD-GMP-INTERVAL-SOL-2354Z.
8 October 2026. Status: EXECUTED BUILD/EXACT FINITE TEST PASS;
INDEPENDENT IMPLEMENTATION REVIEW PENDING.

The authoritative Python reference is SHA-256
`c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace`,
6,604 bytes. The frozen copy is byte-identical. Only `Interval` and `exp_neg`
are oracle targets; the nine-parameter parser/evaluator/report is not ported.
The oracle executes one authenticated byte buffer in memory per test process.
It never substitutes a reread/imported copy or routes values through the
separate Python parameter parser's 256-bit limit.

From this packet directory:

```sh
make BUILD_DIR=/workspace/cloud-gmp-interval-sol-build
python3 tests/differential.py --probe /workspace/cloud-gmp-interval-sol-build/interval_probe --output results
```

The build used `g++ (Debian 14.2.0-19) 14.2.0`,
`-std=c++17 -O2 -Wall -Wextra -Werror -pedantic`, and `-lgmpxx -lgmp`.
Actual return code was zero, with empty compiler stderr. External build budgets
were CPU60s, wall90s, address space1GiB and output-file64MiB. The executed build
record and binary SHA are in [results/build.json](results/build.json). The
binary remains outside the committed packet; its source is preserved.

The final [differential report](results/differential.json) records PASS:

- 2,408 source primitive comparisons matched exact canonical endpoints,
  rational/Boolean results, refusal classes and messages;
- six separate parser contract/refusal/recovery fixtures passed;
- 5,204 exact assertions checked interval order/width, all four signed product
  extrema, division endpoints, signed dyadic containment/grid/width and
  exponential unit/width/zero/large-x contracts;
- cases cover negative/positive/mixed intervals, closed/touching boundaries,
  zero division, reversed and disjoint-unit intervals, integer/Fraction type
  distinction, bad bool/float/string types, invalid precision before shortcuts,
  values around 1 and halving boundaries and around `x=bits`;
- 4,098-bit integer and large/tiny rational inputs, 4,097-bit dyadic precision,
  and a series case above 2,048 bits passed. No primitive 256/2048-bit cap exists.

The deterministic seed is `202610072354`. The full frozen probe input stream
and output records are [differential-inputs.txt](results/differential-inputs.txt)
and [probe-output.jsonl](results/probe-output.jsonl). Their hashes are in the
JSON report. One run preceded addition of an explicit whole-harness wall alarm;
the final recorded run repeated the same inputs/output hashes with that alarm.
There were no failed fixtures in either run and no C++ source change between
the successful build and these runs.

Final budgets: harness CPU90s, wall120s, memory512MiB; C++ process CPU45s,
wall60s, memory256MiB. The final complete fixture/property run took0.186s wall
in this environment, including oracle generation and subprocess work. This is
a dated execution receipt, not a comparative backend benchmark. Typed float
objects occur only in refusal fixtures; certification arithmetic is rational.

The 512-term Taylor-cap and final-width-failure branches are implemented with
the exact source statuses. No valid fixture triggered them. Finite differential
tests do not prove universal equivalence, full330-feature correctness,
native Rust integration, the nine-parameter inverse, observed confidence or
full G6. Root and the independent reviewer own the next integration decision.
