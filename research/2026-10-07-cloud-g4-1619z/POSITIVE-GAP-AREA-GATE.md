# Exact positive-gap gate for the mixed-source leading equations

Contributor: Codex Cloud G4, 7 October 2026. Hand-derived finite algebra/inequality proposition, not a full source return or original G4 endpoint.

Fix one ordered finite sequence of ACTUAL rare-route leading cell parameters, with the same definitions as [the independently accepted mixed-source proof](COLLAPSED-LEADING-MIXED-SOURCE-CONSTRAINT.md). The numbers r,b,k,i retain their coupled physical map. Suppose

    sum r=sum k=sum i=0,

and some r is nonzero. Write `S_j=sum_(h<=j)r_h`, `S_0=S_L=0`. If these proper partial sums do not have both signs, positive chronological gaps cannot solve the full-quartic moment. In what follows assume both signs occur.

Define, using the actual positive own-clocks b,

    B=sum_(j=1)^(L-1)b_(j+1)S_j,
    C0=sum_(j=1)^(L-1)b_(j+1)S_j^2>0,
    A=sum_(j=1)^L S_(j-1)k_j,
    m_plus=min{S_j:S_j>0},
    m_minus=min{-S_j:S_j<0}.

Let

    Cmin=C0+B m_minus, if B>=0;
    Cmin=C0-B m_plus,  if B<0.                   (1)

For this fixed actual coefficient sequence, there exist strictly positive ordinary gap coefficients ell_j satisfying both

    sum_j(ell_j+b_(j+1))S_j=0,
    G7=-(4/3)sum_j(ell_j+b_(j+1))S_j^2+6A=0     (2)

if and only if

    A>(2/9)Cmin.                                (3)

Thus (3) is the exact remaining source-image test for these two chronological leading equations at one fixed architecture. It is not a sufficient criterion for a complete capped response, an isolated finite-epsilon equality, an all-orders analytic return or a fixed-target full-prefix rival. Every other source/forest constraint remains required.

## Proof of the attainable clock cost

Set `D=sum ell_j S_j^2` and impose `sum ell_j S_j=-B`. If B is positive, the total negative-S mass weighted by ell exceeds the positive-S mass by B. Each negative site has `S_j^2>=m_minus(-S_j)`. Therefore

    D>=m_minus sum_(S<0)ell_j(-S_j)
      =m_minus[B+sum_(S>0)ell_j S_j]>B m_minus.

The last inequality is strict because every ell is positive and a positive S occurs. If B is negative, the symmetric argument gives `D>(-B)m_plus`. If B is zero, positive gaps at nonzero S give D>0. Hence every feasible strict clock cost `C=C0+D` lies strictly above (1).

Conversely, choose an arbitrarily small common preliminary ell_j=delta>0. Its remaining signed mass can be corrected by increasing one gap where S has opposite sign, choosing a site of smallest absolute S in that sign. For B nonzero, as delta decreases to zero this feasible cost tends to (1). For B zero, correct the preliminary residual at a site of either required sign; its added cost is O(delta), and C tends to C0. Sites with S=0 retain positive gaps and add no cost. Thus Cmin is the exact infimum within the strict feasible set.

Choose one site p with S_p>0 and one site n with S_n<0. Increase the two gaps along the nonnegative ray

    v_p=-S_n,  v_n=S_p,  all other v=0.

Its signed clock change is zero, while its square cost is

    v_p S_p^2+v_n S_n^2
      =S_p(-S_n)(S_p-S_n)>0.

Starting from a strict feasible cost arbitrarily near the infimum, this ray increases C continuously and without bound while keeping every gap positive and the quartic moment zero. The attainable costs are therefore EXACTLY `(Cmin,infinity)`. Equation G7=0 asks for `C=(9/2)A`, which belongs to this interval exactly under (3).

All chosen gaps implement genuine ordinary survivals `exp(-epsilon ell_j)` at positive epsilon. No negative-time cell is inserted, no source coefficient is varied independently, and no cap-dependent target is created.

## A three-site check of the constants

If `r=(R,-2R,R)` with R positive, the proper partial sums are `(R,-R)` and `Cmin=2R^2 max(b2,b3)`. If actual cells additionally have `k=c r`, then `A=-3cR^2`. The leading equations have positive-gap solutions precisely when

    -c>(4/27)max(b2,b3).

Equivalently the two clock gaps must be equal to `D=-27c/4`, strictly exceeding both applicable own-clocks. This example checks the gate's factors; it does not assert that actual source cells realize the required proportionality or ratios. In particular `c>=0` is excluded by the negative-area sign argument in ACTUAL-COLLAPSED-QUARTIC-FEASIBILITY.md.
