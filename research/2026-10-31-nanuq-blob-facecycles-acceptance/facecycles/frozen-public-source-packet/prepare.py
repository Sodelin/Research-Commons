from pathlib import Path
import hashlib,sys
p=Path(sys.argv[1])
assert hashlib.sha256(p.read_bytes()).hexdigest()=='46902b10c30553fd56099fcc5e1f491391f2d9596631ddd4f2f4284ba5721a70'
s=p.read_text()
a=s.index('theorem IsDrawing.hasFaceCycles_cycleGraph');b=s.index('\n/-! ## The two arcs',a);base=s[a:b]
base=base.replace('hasFaceCycles_cycleGraph','hasFaceCycles_cycleGraph_continuous')
base=base.replace('    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) {e : β}', '    {e : β}')
base=base.replace('h.cycle_isSeparating hpoly hc','jordan_curve_theorem (h.cycle_isJordanCurve hc)')
a=s.index('theorem IsDrawing.hasFaceCycles_union');b=s.index('\n/-! ## `lem:face-cycles`',a);ear=s[a:b]
ear=ear.replace('hasFaceCycles_union','hasFaceCycles_union_continuous')
ear=ear.replace('    (hobl : CrosscutSplitsRegion) (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))\n','')
ear=ear.replace('  have hpoly\' : ∀ g ∈ E(B.union (G.pathGraphOf a D\')), IsPolygonal (edgeArc drawing g) :=\n    fun g hg => hpoly g (hB\'G.edgeSet_mono hg)\n','')
ear=ear.replace('  have hQpoly : IsPolygonal (edgesCover drawing D\') :=\n    h.isPolygonal_edgesCover hpoly hpath.isWalk hne\n','')
a=ear.index('    have hcross := hobl');b=ear.index('    -- Either way,',a)
ear=ear[:a]+'''    have hcross := Nanuq.ContinuousFaceCycles.component_region
      (hB.cycle_isJordanCurve hface.isCycle)
      (show IsCutPair (edgesCover drawing (e :: D)) a b
        (edgesCover drawing D₁) (edgesCover drawing D₂) from
        ⟨harc₁,harc₂.reverse,hunion,hinter⟩)
      hQarc hmeetJ hface.isRegionOf (by rw [hsame]; exact hsub₀) hzF
'''+ear[b:]
ear=ear.replace("hB'.cycle_isSeparating hpoly' hcyc", "jordan_curve_theorem (hB'.cycle_isJordanCurve hcyc)")
a=s.index('theorem face_cycles [G.Finite]');b=s.index('\nend Graph',a);final=s[a:b]
final=final.replace('theorem face_cycles [G.Finite] (hobl : CrosscutSplitsRegion) (h : IsDrawing G drawing)\n    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hG : G.IsTwoConnected)', 'theorem face_cycles_continuous [G.Finite] (h : IsDrawing G drawing)\n    (hG : G.IsTwoConnected)')
final=final.replace('h.hasFaceCycles_cycleGraph hpoly hcyc.isCycle','h.hasFaceCycles_cycleGraph_continuous hcyc.isCycle')
final=final.replace('h.hasFaceCycles_union hobl hpoly','h.hasFaceCycles_union_continuous')
for text in [base,ear,final]:
 assert 'hpoly' not in text and 'hQpoly' not in text and 'hobl' not in text
prefix='''/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué.

Modified derivative proof, not an unchanged upstream file.
Derived from Álvaro Begué's Schoenflies.FaceCyclesProof (Apache-2.0),
upstream pin 05a43d29cde026618777db3d4e4316204ccca237,
source SHA256 46902b10c30553fd56099fcc5e1f491391f2d9596631ddd4f2f4284ba5721a70.
Original proof authorship retained. Continuous-source adaptation: dot, 2026-10-31.
UNCOMPILED CANDIDATE. No fixed taxon order or full NANUQ claim.
-/
import Schoenflies.FaceCyclesProof
import Schoenflies.JordanClosed
import ContinuousRegionCrosscut

namespace Nanuq.ContinuousFaceCycles
open Schoenflies

theorem component_region {C P A₁ A₂ Ω : Set Plane} {p q z : Plane}
    (hC : IsJordanCurve C) (hcut : IsCutPair C p q A₁ A₂)
    (hP : IsArcBetween P p q) (hPC : P ∩ C = {p,q})
    (hΩ : IsRegionOf C Ω) (hPD : P \\ {p,q} ⊆ Ω) (hz : z ∈ Ω \\ P) :
    IsRegionOf (A₁ ∪ P) (connectedComponentIn (Ω \\ P) z) ∨
      IsRegionOf (A₂ ∪ P) (connectedComponentIn (Ω \\ P) z) := by
  obtain ⟨V₁,V₂,h₁,h₂,heq,_,_,_,_,hc₁,hc₂,_,_⟩ :=
    Nanuq.ContinuousRegionCrosscut.continuous_crosscut_region hC hcut hP hPC hΩ hPD
  rw [heq] at hz
  rcases hz with hz | hz
  · exact Or.inl ((hc₁ z hz).symm ▸ h₁)
  · exact Or.inr ((hc₂ z hz).symm ▸ h₂)
end Nanuq.ContinuousFaceCycles

namespace Graph
open Schoenflies
open scoped Graph
variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {a b : Plane}

'''
out=prefix+base+'\n'+ear+'\n'+final+'''\nend Graph
#print axioms Nanuq.ContinuousFaceCycles.component_region
#print axioms Graph.IsDrawing.hasFaceCycles_cycleGraph_continuous
#print axioms Graph.face_cycles_continuous
'''
Path(sys.argv[2]).write_text(out)
print(len(out.encode()),hashlib.sha256(out.encode()).hexdigest())
