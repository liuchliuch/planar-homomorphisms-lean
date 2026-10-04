import PlanarHom.FiniteGraphDisconnectedRank
import PlanarHom.SurfaceDualComponentCount
import PlanarHom.SurfaceRawEmbeddingCode

/-! NEW global homology dimension and cardinality bound from the actual
supplied complement. Disconnected primal graphs, isolated vertices, empty
inputs, and unused ambient handles all remain in the formulas. -/
noncomputable section
open Classical
open scoped BigOperators
open Matrix Module
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn SurfaceRibbonComplement
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G:MultiGraph V E} (R:RotationRows G)

 theorem homology_finrank_disconnected :
    finrank (ZMod 2) R.Homology+Fintype.card V+Fintype.card R.Face=
      Fintype.card E+G.componentCount Finset.univ+R.dualGraph.componentCount Finset.univ := by
  have hG:=G.coboundary_rank_add_components (K:=ZMod 2)
  have hD:=R.dualGraph.coboundary_rank_add_components (K:=ZMod 2)
  have hcycle:=(G.coboundaryMatrix (ZMod 2)).transpose.mulVecLin.finrank_range_add_finrank_ker
  change (G.coboundaryMatrix (ZMod 2)).transpose.rank+
    finrank (ZMod 2) R.cycleSpace=finrank (ZMod 2) (E→ZMod 2) at hcycle
  rw [Matrix.rank_transpose,Module.finrank_pi] at hcycle
  have hquot:=R.faceBoundariesInCycles.finrank_quotient_add_finrank
  rw [R.faceBoundariesInCycles_finrank] at hquot
  change finrank (ZMod 2) R.Homology+(R.dualGraph.coboundaryMatrix (ZMod 2)).rank=
    finrank (ZMod 2) R.cycleSpace at hquot
  omega

 theorem homology_finrank_ribbon_euler :
    finrank (ZMod 2) R.Homology+Fintype.card V+Fintype.card (Boundary R)=
      Fintype.card E+2*G.componentCount Finset.univ := by
  have hh:=R.homology_finrank_disconnected
  have hc:=dual_components_add_isolates R
  have hb:Fintype.card (Boundary R)=Fintype.card R.Face+Fintype.card (Isolated (G:=G)):=Fintype.card_sum
  omega

 theorem homology_finrank_complement_bound (D:Data R) {ambient:ℕ} (hd:D.Valid ambient) :
    finrank (ZMod 2) R.Homology+2*(∑j,D.regionGenus j)≤2*ambient := by
  have hh:=R.homology_finrank_ribbon_euler
  have hb:=D.ribbon_deficit_bound hd
  change Fintype.card E+2*G.componentCount Finset.univ+2*(∑j,D.regionGenus j)≤
    Fintype.card V+Fintype.card (Boundary R)+2*ambient at hb
  omega

 theorem homology_finrank_le (D:Data R) {ambient:ℕ} (hd:D.Valid ambient) :
    finrank (ZMod 2) R.Homology≤2*ambient := by
  have hh:=R.homology_finrank_complement_bound D hd
  omega

 theorem homology_card_le (D:Data R) {ambient:ℕ} (hd:D.Valid ambient) :
    Nat.card R.Homology≤4^ambient := by
  letI : Fintype R.Homology:=Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=ZMod 2),ZMod.card]
  have hh:=Nat.pow_le_pow_right (by decide : 0<2) (R.homology_finrank_le D hd)
  simpa only [pow_mul,show (2:ℕ)^2=4 by decide] using hh

end PlanarHom.PlanarityLRRealization.RotationRows

namespace PlanarHom.SurfaceRawEmbedding.ComplementCode
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization SurfaceRibbonComplement
variable {c:ComplementCode} {g:MixedCode} {bt ut:ℕ} {hg:g.Valid bt ut}
variable {R:RotationRows (g.toMultiGraph hg)} {ambient:ℕ}

 theorem homology_finrank_le (h:c.Valid g hg R ambient) :
    finrank (ZMod 2) R.Homology≤2*ambient := by
  obtain ⟨hw,hv⟩:=h
  exact R.homology_finrank_le (toData hw) hv

 theorem homology_card_le (h:c.Valid g hg R ambient) : Nat.card R.Homology≤4^ambient := by
  obtain ⟨hw,hv⟩:=h
  exact R.homology_card_le (toData hw) hv

end PlanarHom.SurfaceRawEmbedding.ComplementCode
