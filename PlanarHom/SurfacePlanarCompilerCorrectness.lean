import PlanarHom.SurfacePlanarComplementValidity
import PlanarHom.SurfacePlanarComplementMachines
import PlanarHom.PlanarityLRPlanarEuler

/-! NEW ordinary-planar source adapter, with actual computed LR rows and
exact complement construction. No supplied embedding or orientation oracle is
needed to produce the target supplied-surface code. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfacePlanarCompiler
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PlanarityLRDirect
open PlanarityLRConstraints SurfaceRibbonComplement SurfaceRawEmbedding FinitePermutationCycles

 theorem computed_component_genus_zero (g:MixedCode) {bt ut:ℕ} (hp:g.PlanarValid bt ut) (r:Root g) :
    componentGenus g hp.1 (directRotationRows g hp.1 (decideAligned g).2) r=0 := by
  by_cases he:IsEmpty (ComponentEdge g r.val.val)
  · simp [componentGenus,he]
  · letI : Nonempty (ComponentEdge g r.val.val):=not_isEmpty_iff.mp he
    rw [componentGenus,if_neg he]
    apply SurfaceRotationGenus.genus_unique
    have hh:=planar_computed_component_euler g hp r.val r.property
    simpa only [RotationRows.HasGenus,mul_zero,add_zero,Nat.card_eq_fintype_card,
      count,RotationRows.Face,RotationRows.facePerm,componentFace] using hh

 theorem computed_global_capped_euler (g:MixedCode) {bt ut:ℕ} (hp:g.PlanarValid bt ut) :
    g.vertices+Fintype.card (Boundary (directRotationRows g hp.1 (decideAligned g).2))=
      g.edges.length+2*(g.toMultiGraph hp.1).componentCount Finset.univ := by
  have he:=global_capped_euler g hp.1 (directRotationRows g hp.1 (decideAligned g).2)
  have hz:totalGenus g hp.1 (directRotationRows g hp.1 (decideAligned g).2)=0 := by
    simp only [totalGenus,computed_component_genus_zero g hp,Finset.sum_const_zero]
  rw [hz] at he
  omega

 theorem compile_valid (ambient:ℕ) (g:MixedCode) {bt ut:ℕ} (hp:g.PlanarValid bt ut) :
    Input.Valid bt ut ambient (compile ambient g) := by
  refine ⟨hp.1,directRotationRows g hp.1 (decideAligned g).2,rows_realizes g hp.1,?_⟩
  refine ⟨complement_wellFormed ambient g hp.1 (rows g) _ (rows_realizes g hp.1),?_⟩
  exact complement_valid_of_euler ambient g hp.1 (rows g) _ (rows_realizes g hp.1)
    (computed_global_capped_euler g hp)

/-- The graph sent to the surface evaluator is literally the original graph,
so every fixed interaction, unary family and weight has the identical answer. -/
theorem compile_value {C K:Type} [Fintype C] [CommSemiring K] (ambient:ℕ)
    (g:MixedCode) {bt ut:ℕ} (hg:g.Valid bt ut) (M:Fin bt→Matrix C C K)
    (U:Fin ut→C→K) (w:C→K) :
    (compile ambient g).1.evaluate hg M U w=g.evaluate hg M U w := rfl

end PlanarHom.SurfacePlanarCompiler
