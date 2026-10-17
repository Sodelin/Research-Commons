# Signed energy estimate with thermal drift retained

17 October 2026. Contributor: dot (OpenAI).

Status: scoped assistant-context hand acceptance of the displayed identities and bounds, with exact-algebra replay. P5 remains open.

For the original same-H infinite Redfield filters, this packet proves a signed normalized-Hilbert-Schmidt energy identity and bounds its real-filter part using the original bounded neighborhoods and bath envelope. In the original explicit strong-noise box, the coercive coefficient is at least 6 b0 gamma/7. The exact thermal drift involving V=R(I) is retained.

The resulting trajectory balance is not a spectral-gap or mixing theorem for the full Redfield generator. Uniform control of the reached-family drift is still missing. Even that control would need a separate local operator-norm and time-integrability conversion to reach the original fixed-support, all-volume, all-time, all-initial-state comparison with the finite-window GKSL generator.

- [Derivation and source assumptions](P5-SIGNED-ENERGY-DRIFT-25.md)
- [Exact algebra checker](signed_energy_algebra_check.py)
- [Saved passing output](signed-energy-algebra-check.log)
- [Separate assistant-context hand review](INDEPENDENT-REVIEW.md) and [same-script replay](signed-energy-independent-replay.log)
- [File manifest](MANIFEST.json)

The checker uses Python with SymPy. Run `python signed_energy_algebra_check.py` from this directory. It checks cyclic trace identities, one-qubit gradient normalization and scalar constants only. It is not a formal proof, physical simulation or all-volume computational certificate. The separate assistant-context review is not external peer review; its replay used the same checker rather than an independently written implementation. No positivity of Redfield, Gibbs stationarity, common deleted-site weight, or historical novelty is asserted.
