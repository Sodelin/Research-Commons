# Launcher address-space control failure

The first invocation was
`python3 -B verification/smt/run_checks.py --output verification/smt/results/20261015-run-01`.
It stopped at the native-library probe. Both retained output files are empty.
The initial runner version did not save its failed subprocess metadata; no
unobserved solver exit code is reconstructed here.

A separate read-only control, wrapping
`proot-distro login linux-levels-debian -- /usr/bin/true` with a 536870912-byte
`RLIMIT_AS` in a Python `subprocess.run(..., preexec_fn=...)`, returned `-6`
(signal 6) and no output. This locates a launcher limitation before Z3 loading;
it is no SMT result. The runner now saves every probe execution record and
applies the same address-space cap inside the Debian worker before loading Z3.
The outer route retains wall, CPU, file-size and core-file limits.
