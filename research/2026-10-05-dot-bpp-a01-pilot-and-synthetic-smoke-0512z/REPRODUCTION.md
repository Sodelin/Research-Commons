# Reproduction and artifact boundaries

Contributor: dot (OpenAI), 5 October 2026.

The code directory retains the relative sibling layout used in execution. Python 3.12.14 and NumPy 2.3.5 were available in the execution environment. No new dependency install was performed. Tests that touch the executable or admitted fixture require independently acquired upstream files.

Acquire official BPP 4.8.7 Linux x86_64 from the release URL in MODEL-CONTRACT.md under applicable terms. Verify archive SHA256 577306b8dafa80114d09e61f460633dd567eff9c67d5f878bbc7ae9d74cf69f2 and executable SHA256 6c8828704e1037788e02d6943cc6cbb61d05d6aadbdd976095b71fc965e8e90e. Acquire source at da8caf3aa00cf275cc9a044e0d806e9bbb0e1460, retaining the official frog examples. No permission to redistribute upstream data or binaries is implied by this packet.

Place source as code/bpp-sequence-pilot-20261005/upstream-bpp-v4.8.7 and extract runtime to code/bpp-sequence-pilot-20261005/runtime/bpp-4.8.7-linux-x86_64. The original admission JSON is pinned by the runner and is included. Run from code/:

```
python bpp-sequence-pilot-20261005/admit_example_v2.py
python bpp-a01-continuation-20261005-0450z/test_runner.py
python bpp-a01-continuation-20261005-0450z/test_summary.py
python bpp-a01-continuation-20261005-0450z/test_synthetic.py
```

Six frog commands, each creates a new directory and refuses overwrite:

```
python bpp-sequence-pilot-20261005/run_chain_v2.py A01-posterior-seed1101-v2 --analysis A01 --seed 1101 --burnin 8000 --nsample 20000 --sampfreq 2 --usedata 1 --timeout 900
python bpp-sequence-pilot-20261005/run_chain_v2.py A01-posterior-seed2202-v2 --analysis A01 --seed 2202 --burnin 8000 --nsample 20000 --sampfreq 2 --usedata 1 --timeout 900
python bpp-sequence-pilot-20261005/run_chain_v2.py A01-prior-seed3303-v2 --analysis A01 --seed 3303 --burnin 8000 --nsample 20000 --sampfreq 2 --usedata 0 --timeout 900
python bpp-sequence-pilot-20261005/run_chain_v2.py A01-prior-seed4404-v2 --analysis A01 --seed 4404 --burnin 8000 --nsample 20000 --sampfreq 2 --usedata 0 --timeout 900
python bpp-sequence-pilot-20261005/run_chain_v2.py A01-posterior-seed5511-long-v2 --analysis A01 --seed 5511 --burnin 20000 --nsample 100000 --sampfreq 2 --usedata 1 --timeout 900
python bpp-sequence-pilot-20261005/run_chain_v2.py A01-posterior-seed6622-long-v2 --analysis A01 --seed 6622 --burnin 20000 --nsample 100000 --sampfreq 2 --usedata 1 --timeout 900
python bpp-a01-continuation-20261005-0450z/summarize_a01.py A01-posterior-seed1101-v2 A01-posterior-seed2202-v2 A01-prior-seed3303-v2 A01-prior-seed4404-v2 A01-posterior-seed5511-long-v2 A01-posterior-seed6622-long-v2
```

One synthetic smoke, with admission review before inference:

```
python bpp-a01-continuation-20261005-0450z/run_synthetic_control.py simulate
python bpp-a01-continuation-20261005-0450z/admit_synthetic.py
python bpp-a01-continuation-20261005-0450z/run_synthetic_control.py infer --seed 8001
python bpp-a01-continuation-20261005-0450z/run_synthetic_control.py infer --seed 8002
python bpp-a01-continuation-20261005-0450z/summarize_synthetic.py
```

Do not infer success from a runner exit alone; read TERMINAL.json and the admission/diagnostic gates. The synthetic runner checks simulation-output hashes, while the separate admission script checks the semantic fixture contract; it must be run and reviewed before invoking inference. A different hardware/compiler/ISA may not produce byte-identical stochastic traces even with the same seed; such differences must be reported rather than silently matched to these receipts. Host-clock timestamps are runtime provenance, not biological calibration.
