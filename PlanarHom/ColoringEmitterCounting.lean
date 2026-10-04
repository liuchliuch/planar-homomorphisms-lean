import PlanarHom.ColoringCanvasPaletteCount
import PlanarHom.ColoringIncidenceComponents
import PlanarHom.ColoringEmitterIncidenceEquivalence
import PlanarHom.ColoringEmptyRecovery
import PlanarHom.PottsComponentCode

/-! NEW final literal-count and exact-division recovery join. The required
numeric incidence equivalence is supplied by the actual emitter allocation
module. The actual count and empty-aware exact recovery are kernel checked. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open Complexity ParsimoniousNorOneInThree ProperColoringPottsReduction MultiGraph

 theorem totalColorings_nonempty (f:NumericFormula) (hf:NumericValid f) (hne:f.2≠[]) :
    totalColorings 3 (compile f)=6^componentCount f*CountingPositiveOneInThree.count f := by
  let i:=Canvas.compile_incidenceEquiv f hf hne
  have hc:(Canvas.graph f).componentCount Finset.univ=componentCount f :=
    i.componentCount_eq.symm.trans (GraphComponentCode.componentCount_eq_components_length (compile f) (compile_valid f))
  calc
    _ = properColoringCount ((compile f).toMultiGraph (compile_valid f)) 3 := by simp [totalColorings,compile_valid]
    _ = properColoringCount (Canvas.graph f) 3 := i.coloring_count.symm
    _ = _ := by
      rw [ColoringCanvasBoolean.canvas_count f hf hne,hc]
      simp only [CountingPositiveOneInThree.count,Nat.card_eq_fintype_card]

 theorem recover_correct (f:NumericFormula) (hf:NumericValid f) :
    recover (f,[totalColorings 3 (compile f)])=CountingPositiveOneInThree.count f := by
  by_cases hne:f.2=[]
  · obtain ⟨n,cs⟩:=f
    dsimp only at hne
    subst cs
    exact recover_empty_correct n
  · rw [recover,totalColorings_nonempty f hf hne]
    simp only [unusedOriginal,if_neg hne,pow_zero,one_mul,List.headD_cons]
    exact Nat.mul_div_cancel_left _ (pow_pos (by decide : 0<(6:ℕ)) _)

end PlanarHom.ColoringEmitter
