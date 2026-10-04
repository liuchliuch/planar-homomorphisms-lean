import PlanarHom.PlanarityLRFaceRepresentatives
import PlanarHom.PlanarityLRDrawnTreeAxiomAudit

/-! NEW face-orbit semantic regressions. -/
namespace PlanarHom.PlanarityLRRealization.Regression
open Complexity PlanarityLRRawConstraints.Regression
open PlanarityFaceCode
example (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool) :
    ((representatives g bits).flatMap (boundary g bits)).Perm (PlanarityRotationCode.allDarts g) :=
  all_boundaries_perm_allDarts g hg bits
example : walk (completeGraph 0) [] (0,false) 0=[] := rfl
#eval fullTable (completeGraph 0) []
#eval fullTable (completeGraph 1) []
#eval fullTable (completeGraph 2) []
#eval fullTable ⟨1,[(0,(0,0))],[]⟩ []
end PlanarHom.PlanarityLRRealization.Regression
