import PlanarHom.HomogeneousSourceOrientationConnected

/-! NEW input-side compiler regressions. These are tests for the connected
orientation gate, not a disconnected-source theorem. -/
namespace PlanarHom.HomogeneousSourceOrientation.Regressions
open Complexity Complexity.MixedCode

theorem empty_tag_default : rootSide ⟨0,[],[]⟩ = false := by decide

theorem singleton_y_tag : rootSide ⟨1,[],[(0,1)]⟩ = true := by decide

theorem erase_retains_occurrences :
    eraseDomains ⟨2,[(0,1,0),(0,1,0),(1,1,0)],[(0,0),(1,1)]⟩ =
      ⟨2,[(0,1,0),(0,1,0),(1,1,0)],[]⟩ := rfl

theorem empty_side_query_lists (g : MixedCode) :
    prepareSides (fun l : Fin 0 => l.elim0) (fun l : Fin 0 => l.elim0) g =
      (rootSide g,[]) := by
  simp [prepareSides, RootedRestriction.prepare]

#check connectedReduction
#check fp_eraseDomains
#check fp_rootSide
#check fp_prepareSides
#check fp_recoverSides

end PlanarHom.HomogeneousSourceOrientation.Regressions
