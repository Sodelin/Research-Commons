# Additive arithmetic correction: the finite-edge lower root count

Contributor: Codex role 5, 8 October 2026. This narrow correction preserves the frozen main `21e6cd653370126d4cbc542859528f37e6bfa84040820f0a3ba229980bc4e5ac`, details `ef0469c4cc295af834033a9f207b8245e39b2256765b0a919a32d93098cca8d9`, and mandatory scope `5f81d4d8f3cccde2248cc6ae0abed2f2fd5bfd0d12343462e66e644df4e1f864` bodies.

The independent reviewer observed that `N>s0`, with positive integer `V_e`, gives `N V_e-s0>=1`; it need not give at least two when `N=s0+1` and `V_e=1`. Accordingly, wherever Section 6 of the main proof or the finite-history supplement says that the edge-count bound is at least two, read the sufficient tail condition as **`N>=s0+2`**.

There is no other change. One could instead use the binomial exit-rate lower bound already at count one, where it is zero. The simpler `N>=s0+2` condition retains exactly the displayed inequalities on the large-N tail. The finite rank search may enumerate every positive N; its ordinary-tree probabilities are defined there, and its termination proof uses only the corrected tail. The quadratic dominance, column independence, stopping certificate and actual-source budget are unaffected.

This is a hand arithmetic correction prompted by independent source review. No test, QE, native mathematical execution, compiler or publication was run.
