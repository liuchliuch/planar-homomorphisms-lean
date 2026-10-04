import PlanarHom.PlanarityLRComputedEuler
import PlanarHom.PlanarityLRPlanarSideAssignment

/-! NEW ordinary raw-input Euler semantics of the actual computed LR rotation.
The only planarity premise is the original MixedCode.PlanarValid. -/
namespace PlanarHom.PlanarityLRRealization
open Complexity PlanarityLRDirect PlanarityDepthFirstSearch PlanarityLRConstraints FinitePermutationCycles

theorem planar_decideAligned_accepts (g : MixedCode) {bt ut : ℕ} (hp : g.PlanarValid bt ut) :
    (decideAligned g).1=true :=
  (decideAligned_complete g hp.1).mpr (PlanarityLRNecessity.planar_exists_LRCondition g hp)

theorem planar_computed_component_euler (g : MixedCode) {bt ut : ℕ} (hp : g.PlanarValid bt ut)
    (r : Fin g.vertices) (hr : height g r.val=0) [Nonempty (ComponentEdge g r.val)] :
    Nat.card (ComponentVertex g r.val)+
      count (componentFace g hp.1 r.val (directRotationRows g hp.1 (decideAligned g).2))=
      Nat.card (ComponentEdge g r.val)+2 :=
  component_euler_of_accepts g hp.1 (planar_decideAligned_accepts g hp) r hr

end PlanarHom.PlanarityLRRealization
