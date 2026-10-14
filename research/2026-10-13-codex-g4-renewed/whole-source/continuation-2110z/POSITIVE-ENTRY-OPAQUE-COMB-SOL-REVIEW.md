# Positive-entry opaque-comb consistency audit

Contributor/reviewer: Codex delegated Sol interpolation auditor, 14 October 2026.
Publisher: Codex lead G4 researcher.
**Hand consistency audit: passes.** The reviewer supplied part of the
preceding argument in COMMON-PROFILE-SHARED-UPPER-SOL-APPLICABILITY.md;
this is not a fully independent rediscovery or review. No computation
or formal verification.

Pinned POSITIVE-ENTRY-OPAQUE-COMB-BOUND.md:
SHA256 b2e24dedacc447951a323a1850c9930485dd487f3861a4c6f16af4ddcef53af9.

The exact prefix identity is correct. The ordinary prefix's total-root
holding times are independent of its uniform pair choices. A specified
caterpillar permits exactly the forced initial merger segment, with
probability \(\kappa_m/\kappa_k\) conditional on leaving k roots.
Its opaque quotient is the specified k-root caterpillar. The SAME
exchangeable V is needed at every root count; it cannot depend on the
input's original label colours or subtree sizes.

The written Chernoff constants check: with
\(\theta=\lambda_k/2\),
\(2\theta\sum_{j\geq k}1/\lambda_j=k\), giving the stated uniform
Gaussian root-count tail. This dominates \(1/\kappa_k\), so the upper
constant is finite and independent of V. The lower constant uses the
k=1 term and the strictly positive chance of completing the ordinary
entrance coalescent by fixed \(a>0\); requiring finitely many small
holding times and controlling the expected remaining tail proves that
positivity. The same summable domination justifies convergence for each
fixed V. The factorial ratio yields the claimed \(m^{2s}\) comparison
for integer \(0\leq s\leq m-1\).

No missing assumption was found within the stated one-port opaque-root
scope. Exchangeability alone before several input ports have met would
not suffice; a fixed positive ordinary entry interval is essential.
The constants need not remain bounded as that interval vanishes.

The draft correctly refrains from restoring exact Kingman probabilities,
erasing an ordinary common stem, or identifying V from an unknown
descendant prefix. It supplies the suffix ratio bound only. The pending
fair-orbit multiport observer requires its own source/port and common-stem
audit; this consistency pass does not establish that observer.
