# Mandatory admission threshold for the finite witness search

21 October 2026. A substantive source-specification correction, not a
new execution or independent acceptance. The main counterexample and
I13/G4 proofs already assume N sufficiently large. Their mathematical
bounds are unchanged. The search wording must also enforce that
condition BEFORE interpreting a returned value as an admitted witness.

This corrects the unrestricted q enumeration wording in
P5-FINITE-WITNESS-SELECTION-v1.md, SHA256
01f23003ae3292ce0a7f41328c0e6b52b688a7adef29f2f212459512f72fbc06,
and supplies the starting condition for the search paragraph of
P5-FINITE-GRID-COROLLARY-v1.md, SHA256
1f4389f3877c8d085320a8a81c265bda9f679a3e0209244f065a8defe9cec07d.
Those frozen sources retain their bytes and history. No search has run.

## Why this condition is necessary

The clock mixture weight is w=(kappa(t_N)+1)/(2kappa(t_N)). Its
positivity is proved by C2 only when t_N<=a0/(2b^2), b=38gamma and
a0=gamma*y^2/6912. Merely enumerating q>=1 without this restriction
would not prove each input mixture positive. A large output at an
unqualified early q could therefore not be accepted as a P5 witness.
The corrected procedure below enumerates ONLY qualified volumes.

For arbitrary computable fixed parameters one may dovetail strict
eligibility certificates with the prediction evaluation, retaining only
sizes with certified t_N<a0/(2b^2), bt_N<log(2)/4, U_N>2 and
exp[-(S_N/tau)^2]<b_G/2. All sufficiently large sizes qualify.
The following explicit dyadic family avoids those certification decisions.

## An entirely explicit starting depth

Fix ANY integer ell>=40 and use

 gamma=1, tau=2^(-ell), Gamma=9/4,
 J=eta_0=b_G/32, omega_0=b_G/96,
 N=2^(q+1)-1 with q>=q_min=4ell+80.                 (A0)

The other constants, all baths and physical terms are exactly those of
the candidate, with epsilon_clock=1/32. For a computable clock length
use the certified integer rounding variant already proved in G's search
paragraph, consistently throughout the construction and finite bound.

First,1/2<b_G<1. The upper bound follows from its formula. For the lower,
exp(-1/8)>=7/8, exp(-1/128)>=127/128 and
sqrt(pi/8)>3/5 because pi>3. Thus

 b_G>(7/8)(3/5)(127/128)=2667/5120>1/2.

It follows that y=Jtau>tau/64 and

 a0>tau^2/(4096*6912),
 t_*=a0/(2*38^2)>tau^2/10^11.                     (A1)

Indeed2*38^2*4096*6912<10^11. From N>=2^q and A0,

 t_N=N^(-1/2)<=2^(-q/2)<=tau^2*2^(-40)<t_*.

Therefore kappa(t_N)>=1, every clock mixture is a positive normalized
physical density, and its logical functional is positive of norm1 at
every duration in[0,t_N]. All interpolation keeps that same fixed density.

Moreover bt_N<=38*2^(-40)<1/8<log(2)/4, where log(2)>1/2 follows by
integrating1/x on[1,2]. Also U_N=N^(1/4)>2. Since

 S_N/tau=N^(1/3)/(1000 b_G tau)>2^ell/1000>2,

its Gaussian tail is less than exp(-4)<1/16<b_G/2. The W1 condition
then follows from6eta_0 R_N S_N=6/1000 and bt_N<log(2)/4.
Finally y<tau/32<1/288 and

 Gamma*tau=(9/4)2^(-ell)<=1/(360*2^30)

because2^10>810. Thus the original fixed parameter box, the positive
initial density and every elementary domain condition used in I13/G4
hold at EVERY enumerated q, not just at the eventual successful q.

## Corrected selection rule and its precise scope

For integer target B>=2 start the finite-grid dovetail search at
q>=4ell+80, and on subsequent searches also require q greater than the
last returned depth. Use only the stated real r/u/time/v grids and the
original full filters. Stop only when a certified interval for the
actual prediction has modulus strictly greater than B. The candidate's
eventual G4 bound guarantees termination CONDITIONAL on the full proof;
every tested input is already admitted by A0-A1 and the physical bath/
geometry suppliers, independently of whether it produces a large value.

This restriction changes neither the asymptotic result nor its fixed
local observable. It prevents an uncertified small-volume initial state
from being mistaken for a counterexample. All arbitrarily small dyadic
x=(9/4)2^(-ell), ell>=40, keep the same b0,j,k,m,nu across their volume
families. The same beta=tau/8 is fixed across every family. No practical
runtime, computed witness or formal verification is claimed.
