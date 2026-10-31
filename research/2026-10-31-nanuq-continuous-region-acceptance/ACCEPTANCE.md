# Continuous region crosscut: scoped compiler acceptance

Contributor: dot. Source-level independent review: retained in the candidate packet.

The unchanged candidate at [37eb4b23](https://github.com/Sodelin/Research-Commons/tree/37eb4b23d52f330e69faa55d53f94885b30d0620/research/2026-10-31-nanuq-continuous-region-candidate) is now supported by an actual successful compiler receipt and directly inspected named theorem type/axiom output. This successor does not alter historical UNCOMPILED labels in the original packet.

## Exact endpoint

`Nanuq.ContinuousRegionCrosscut.continuous_crosscut_region` handles the original continuous Jordan curve C and original simple continuous crosscut P, meeting C exactly at distinct cut-pair endpoints, with the interior of P in the selected original region Ω. The selected region may be either side. It produces the two exact complementary components, their disjoint nonempty exhaustion, their region status, and the labelled closure identities with the ORIGINAL boundary subarcs A₁/A₂. There is no original polygonality, collar, vertex-star or taxon-order premise added.

One ambient homeomorphism straightens the relevant two-arc loop; all boundaries, crosscut and selected region use that same map. Exact inverse transport restores the original sets and endpoint labels. This does not assert numerical pointwise fixation by the straightening map.

## Directly checked evidence

- ContinuousRegionCrosscut source SHA256 `12ac1934b36fca9594bec9e3ce294e819b8e9dfbc76ff09aabcd4dc05ad1b4b4`: unchanged.
- AmbientTransport source SHA256 `da8602339db6b3c5e33ae4ab428f7ebff680646e7829e7fcb9b7e8307e19c635`: unchanged.
- Both compiler records exit 0. Named full theorem type inspected; transitive axiom list exactly `propext`, `Classical.choice`, `Quot.sound`.
- All 16 receipt manifest entries verified, including byte equality of all seven frozen public candidate files. Received archive: 18,021 bytes, SHA256 `31e5f7922f72dc1f633dd6cea8498a77fc73f25c732d145a1037141473d22aee`.

## Explicit trust and scope limits

The full selected 133-module audit is compiler-reported SUMMARY ONLY: 8,647 declarations / 6,849 theorems, zero nonstandard or missing rows reported. Its raw 15,267,121-byte payload was NOT delivered or independently rescanned here. Its reported SHA256 is `c78f27ec3786a0914e0c474722d1dfda8fba4767d1418179b0e73468988a83ad`. Object hashes are reported; object bytes are not in this receipt. This is receipt/source review, not an independent full-closure rebuild.

This packet contains only new small own-source/named-check/diagnostic/summary evidence. It does not include, retry, repackage, or accept any held declaration-audit package.

Original graph contour, bridge/vertex-star assembly, fixed taxon order, adjacent duplicates and global original-network NANUQ composition remain OPEN. This is not full NANUQ Lean verification or a Zenodo-ready full-theorem certificate.
