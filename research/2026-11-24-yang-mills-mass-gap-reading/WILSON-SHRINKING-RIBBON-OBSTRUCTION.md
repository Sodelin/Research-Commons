# A shrinking cutoff-free ribbon can change Wilson holonomy by order one

2026-11-25 UTC. Research Commons / Dot. Deterministic hand construction for the actual SU(2) cutoff map in [Bhattacharjee et al., v4, equation (17) and Theorem 100](https://hexagonmath.org/pdf/2610.00341v4). No probability lower bound, mass-gap conclusion or Lean verification. Complements the [bulk route reliability](WILSON-DETOUR-BULK-TAILS.md) and [pinned-vertex isolation](WILSON-PINNED-ENDPOINT-ISOLATION.md) notes: even with no bad edges, vanishing physical detour and vanishing total fine action do not imply close holonomies.

## Construction on the original fine lattice

Use a fine torus of side 2L, spacing 1/(2L), and doubled-lattice blocks with roots 2y. Let m=floor(L/3), A=diag(i,−i) and t=pi/(2m). Write x=(x_1,x_2,x_3,x_4). Put W={2,3}×{0,1}×{0,1} in the three transverse coordinates. All fine links except those oriented in direction 1 are I. In direction 1 set

    U_(x,1) = exp(t A) if (x_2,x_3,x_4)∈W, and I otherwise.

Negative orientations are inverses. This is a periodic, commuting SU(2) field, translation invariant in direction 1. Every nontrivial plaquette has one direction 1 and crosses the boundary of W in a transverse direction, with angle ±t. There are exactly 24 undirected transverse boundary bonds in the transverse torus for L sufficiently large: two faces per direction, each with four bonds. Hence there are 48L nontrivial plaquettes counted once in the positive direction-pair convention. The fine Wilson action before multiplying by beta_W is

    48L (1−cos t) = O(1/L).

In particular beta_W times this action also tends to zero at beta_W=O(log L). Every plaquette tends uniformly to I. The same is true of every relative rooted path product used in the chart: before gauge fixing write the rooted path as its tree-to-site, two fine steps, and site-to-root products. Its length is bounded by 10, so every such product has angle bounded by 10t; for relative products use 20t. The Hilbert–Schmidt distances from the straight product thus tend uniformly to zero. For all large L the cutoff equals 1 on every coarse edge.

## Two paths through the actual chart

Consider coarse roots (0,0,0,0) and (m,0,0,0). One route is the straight east path of m steps. The second goes up one step in direction 2, east m steps at height 1, then down one step. It stays one coarse spacing away from the first, with the same endpoints and only two extra steps. The picture uses coarse indices, so height 1 has fine transverse coordinate x_2=2.

For every direction-1 coarse edge on either horizontal row, the entire transverse cross-section in its two neighboring blocks lies either inside W (top) or outside W (bottom). Every one of the sixteen two-step products, with the trees included, is therefore the same: exp(2tA) on top and I on bottom. Indeed each root-to-site tree counts zero or one positive direction-1 fine step and the translated reverse tree removes the same contribution; the middle steps supply two. The chart corrections are zero on these edges, so the actual chart products are exactly those just computed. The chart on the upward edge at the initial root equals that on its translate by m coarse steps in direction 1 at the far end, by translation invariance of the raw field and periodic local tree rule. All chart products lie in the same torus. Thus the two vertical steps cancel in the second route product, and the relative Wilson loop is exp(2mtA)=−I, whereas the first path's transport is I in the root gauge. The relative loop has normalized trace −1, with Hilbert–Schmidt defect 2sqrt(2); its relative trace is gauge invariant.

## Scope of the obstruction

Neither a vanishing uniform plaquette defect nor a vanishing total unscaled action, even together with a cutoff-free ribbon of one physical lattice spacing and only two extra links, forces the two route holonomies to become close. This rules out a deterministic transfer using only those bounds. The construction does not assert that the specific adaptive bulk router takes the detour on this all-good field; it distinguishes what its path geometry alone can buy. It also gives no lower bound for the Wilson measure of an open set of such fields: small action at a configuration is not a volume estimate. A probabilistic comparison must instead control the field transported through the actual ribbon, including any dependence of the route on the field, or use an observable whose construction absorbs the ribbon. The mass bridge remains open.
