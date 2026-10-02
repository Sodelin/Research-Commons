# G4 original-hybrid independent live-root routing bridge

Dedicated Sol6.1 formalization contribution, 2026-10-02. Original Samuel graph
source and the G4 research lane's derivation are retained. The polynomial source
is [FOUR-ROOT-PLACEMENT.md, immutable 3d755ef](https://github.com/Sodelin/Research-Commons/blob/3d755ef391066069d33ff4490da65f00742b7ea7/research/2026-10-01-sol61-g4-allcopy-2237z/FOUR-ROOT-PLACEMENT.md).

[Lean source](program/G4IndependentRoutingBridge.lean),
[exact theorem signatures/axioms](receipts/VerifiedRoutingBridge.log),
[successful dependency/hash/resource receipt](receipts/G4IndependentRoutingBridge-receipt.json).

## What now follows from explicit definitions

The input index Fin n represents n LIVE roots of the current ancestral forest.
An earlier coalesced root can retain several original copy labels; it still gets
one coin, as in the compiled G2 LiveAncestry interface. The module never replaces
this with one new coin per original copy.

A coin assignment maps every live root to Bool. Its independent probability
weight is the product of u on parent0 and 1-u on parent1. Lean proves all
assignment weights sum to1, and that they are nonnegative for 0<=u<=1. It proves
the two parent root counts sum to n.

The parent edges are the actual distinct original incoming edge IDs at an
admitted RootedBinary hybrid. Lean proves that Boolean root counts equal the
cardinalities of roots routed to each named original parent edge. Original
parent identities are not merged or replaced by compressed actuator IDs.

For any fixed arm kernels a(k),b(k), private independent arm no-merger probability
is defined by summing those normalized routing weights times a(number in parent0)
and b(number in parent1). Lean enumerates n=2,3,4 assignments exactly. The G4
s2/s3/s4 polynomials are conclusions of this sum, given the explicit finite arm
contract a(0)=a(1)=1,a(2)=x,a(3)=x^3,a(4)=x^6 and the analogous y contract.
No desired bigon polynomial appears as an input premise.

The same original hybrid, u and arm kernels are held fixed at every input size.
This local model uses independent live-root coins and private arm processes.
It is not asserted for a retained shared parent register or a whole-locus
common-mixture pulse.

## Explicit continuous-time holding model

For k<=1 the first-holding no-merger event is deterministic. For k>=2, the
module uses Mathlib's exponential probability measure with rate choose(k,2).
It proves the corresponding survival probability is exp(-t)^choose(k,2) for
nonnegative duration t. Thus the finite arm contract above is itself proved for
this explicitly defined exponential first-holding model, and the final
`exponential_model_original_coordinates` theorem needs no arm-power premise.

This is the expected total unit-rate unordered-pair hazard model. Identifying
its holding clock and the private-arm product with the actual admitted Kingman
source process is still a source-generator obligation. The module does not
assume that desired identification as an unproved Lean axiom. Complete unranked
forest generators, private-context composition, endpoint transfers and
observable/tomographic recognition remain separate formal obligations.

## Actual compiler evidence and limits

Lean4.33.1, pinned mathlib; one thread, 4 GiB cap and 120-second timeout.
Compilation exit0 in3.710887 seconds, peak child RSS3,168,320 KiB (3.02 GiB).
The previously compiled G1 exponential-measure import sets most of this memory
floor; the routing-only prototype was about1.8 GiB. No heavy legacy source
certificate was retried.

Successful source SHA256:
`e30d82ea7e57138d463c779205dfcf686b520cb649d9d5767ee3c13853f19f6b`.
Printed axioms are exactly propext, Classical.choice and Quot.sound; no
sorryAx/custom unproved axiom occurs in the completed proof dependency audit.
