import PlanarHom.FisherExpansionCodeSemantics
import PlanarHom.FisherCubicCodeSemantics
import PlanarHom.FisherIncidenceAlgebra

/-! NEW validity and cubic-incidence obligations for the actual two-stage
numeric compiler, derived from the original abstract expansion theorem. -/
noncomputable section
open Classical
namespace PlanarHom.FisherCodePipeline
open Complexity MultiGraph Fisher
variable {g : MixedCode} {bt ut : ℕ} (hg : g.Valid bt ut)

include hg

 theorem intermediate_valid : (intermediate g).Valid 1 0 := FisherExpansionCode.computed_valid g hg

 theorem intermediate_cubic : ∀v,((intermediate g).toMultiGraph (intermediate_valid hg)).selectedDegree Finset.univ v=3 := by
  intro v
  let i:=FisherExpansionCode.computedIncidenceEquiv g hg
  obtain ⟨q,rfl⟩:=i.vertex.surjective v
  exact (i.degree_univ q).trans (expansion_is_cubic _ q)

 theorem valid : (code g).Valid 1 0 := FisherCubicCode.valid (intermediate g) (intermediate_valid hg) (intermediate_cubic hg)

end PlanarHom.FisherCodePipeline
