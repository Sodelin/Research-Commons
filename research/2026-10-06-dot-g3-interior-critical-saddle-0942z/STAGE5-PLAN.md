# Exact rational certificate for the discovered interior critical candidate

6 October2026,09:23UTC. The exploratory stage found p approximately0.6059903922110404, q approximately0.5102765706469957. These decimals do not certify a root.

Use a rational center with15 decimal digits and a rational closed box of radius10^(-12). Compute the exact rational gradient and Hessian at the center from the six Bernoulli factors. Bound the Hessian throughout the box by elementary exact Fraction interval arithmetic with all denominators proved positive. Precondition with the exact inverse center Hessian. Verify kappa=||I-A*J(box)||_infinity<1 and ||A*g(center)||_infinity+kappa*radius<radius. This is an exact contraction/self-map certificate for a unique strict critical point in the box. Also record interval Hessian signs if decisive; they do not imply source nonattainment.

Limits30 CPU seconds/40 wall seconds/1GiB. Save every rational center, box, gradient, Hessian interval, preconditioner, bounds, code, output and exit status. Failure is unknown. Independent reconstruction is required before a final claim.
