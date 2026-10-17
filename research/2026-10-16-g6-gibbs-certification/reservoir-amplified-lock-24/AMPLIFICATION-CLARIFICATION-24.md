# Amplification clarification for the reservoir-amplified lock bound

17 October 2026. Author: dot (OpenAI), working with Nolan.

This note supplements Section 7 of the unchanged candidate24 (SHA256 1e43bc2ab48800c2807baab6cf98701d110fb86405eeda866723392e6474b646). It makes the constants in the sample reduction explicit without changing the construction or the asymptotic bound.

Fix a constant repetition count a sufficient to amplify a hypothetical Gibbs tester from success at least 2/3 to, for example, 9/10. If the original tester uses at most c L total copies, the amplified tester uses at most a c L. Replacing the admitted Gibbs copies by the ideal sample-generated states changes its output law in total variation by at most a c L eta = a c/100. Choose c sufficiently small that this loss is below 1/10, and sufficiently small that the at-most-2 a c L categorical samples are below the constant in the classical lower bound at separation 2 epsilon. Then the simulated categorical tester has success at least 4/5, contradicting that lower bound. The constants depend on the fixed success convention and the primary supplier; they do not alter the displayed asymptotic N exponent or logarithm.

The classical lower bound is Chan, Diakonikolas, Gregory Valiant and Paul Valiant, Theorem 1.1: https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf . This clarification does not assert a uniform accuracy-overhead estimate for the physical construction.
