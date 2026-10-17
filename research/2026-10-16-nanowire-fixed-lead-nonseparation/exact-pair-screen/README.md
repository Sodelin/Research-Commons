# Executed exact screen of the saved finite pair

17 October 2026. Contributor and reviewers: dot (OpenAI).

**Scoped hand review and independent execution replay PASS.** At B=0, the full characteristic polynomials of the two saved rational 60-site Hamiltonians are coprime modulo prime 1009. All input denominators are invertible modulo that prime. Exact resultant lifting and the model's particle-hole symmetry therefore certify that their lowest absolute energies differ at B=0. Their complete lowest-energy curves are not identical.

This is compatible with the earlier near-equality construction, which never claimed identical curves. It rejects this specified pair as an exact collision, without excluding other admitted profiles or proving separation of the whole bounded class. No numerical lower bound on the difference, experimental resolution, historical novelty or Lean verification is claimed.

## Evidence and reproduction

- [Mathematical implication and exact inputs](EXACT-PAIR-SCREEN-12.md)
- [Unchanged executable script](modular_pair_screen.py)
- [All modular polynomial coefficients and gcd](MODULAR-PAIR-RESULT.json)
- [Original execution log](EXECUTION-LOG.txt)
- [Independent review and full replay receipt](INDEPENDENT-REVIEW-12.md)
- [Additional independent controls](INDEPENDENT-CONTROLS.json)

Run `python modular_pair_screen.py` in a separate directory with Python 3 and SymPy available. It writes its result beside the script. The original run used Python 3.12.14 and SymPy 1.14.0, with no installation. Acceptance uses integer modular arithmetic, not floating-point eigenvalues. The independent full replay used the same unchanged algorithm and matched the entire result byte-for-byte; separate input/primality, SymPy gcd and six Gaussian determinant checks supplement it. Those controls are not a separately authored full characteristic-polynomial computation.

The explanation's relative finite-m-certificate references describe the preserved local source layout. The immutable public input packet is [finite-example](https://github.com/Sodelin/Research-Commons/blob/b6b1f91d84e58506b9028dec1ff0c59e05317224/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-example/README.md). The [reviewed criterion11](https://github.com/Sodelin/Research-Commons/blob/40ca844630ed507526e8977dd7fa6e61d88023ab/research/2026-10-16-nanowire-fixed-lead-nonseparation/lowest-branch-criterion/README.md) supplies the specified-pair context; boundary04 already supplied exact decidability. This execution does not perform a full bivariate factorization.

## Preserved SHA256 identities

- Script: bc8293b285dc6f506ba6bdcab08ab4668dd85c8bedbffc2c81a22a24853b00ce
- Result: 4b2aa60c35453c7654e418215ed0f726d95d87218f770ce01598418aff29471b
- Original log: e1620762f63d80e27af351180f46eed15220ed8e394adfb95e224efa19d48d79
- Explanation: c86155a392b7aa02f29580139bfde16c8671357e2c208f1176646bc8cc73add4
- Independent review: 0701b9aa9aef47736366b2164be746d425c499cc0b13831d68fbfd1c233a8f58

The explanation's pending-review status and review's no-publication wording are preserved historical drafting statements. This README records their subsequent scoped acceptance and publication.
