import PlanarHom.SurfaceWeightedClassTractability
import PlanarHom.FiniteFieldQuotientLanguage

/-! NEW supplied-row actual-row quotient algorithm, preserving the sum of original vertex weights and the original number-field codec. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceWeightedBlockTractability
open Complexity Complexity.MixedCode IsingTensorTractability SurfaceRowEvaluation
variable {ambient : ℕ}
variable {C : Type} [Fintype C] {dimension : ℕ}

/-- Literal Theorem 1.3 structural sufficiency in any fixed original real
number field. Neither quotienting nor extension-field descent changes the
original raw input language or the prescribed output codec. -/
theorem positiveVertexWeightClass_inFP_of_ising (hIsing : SurfaceRowEvaluation.PositiveIsingFoundation ambient) (K₀ : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ K₀] (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Matrix C C K₀) (w : C → K₀)
    (hs : ∀ i j, (M i j : ℝ) = (M j i : ℝ))
    (h : Structures.PositiveVertexWeightClass (fun i j => (M i j : ℝ))
      (fun i => (w i : ℝ)) hs) :
    (SurfaceRowEvaluation.Evaluable ambient basis (fun _ : Fin 1 => M) emptyUnaries w) := by
  let hsK : ∀ i j, M i j = M j i := fun i j => Subtype.ext (hs i j)
  let e := FiniteFieldQuotientLanguage.realQuotientEquiv M
    (fun i j => (M i j : ℝ)) (fun _ _ => rfl)
  let N := fun i j => Twins.quotientMatrix M hsK (e.symm i) (e.symm j)
  let v := fun i => Twins.quotientWeight M w (e.symm i)
  have hN : (fun i j => (N i j : ℝ)) =
      Twins.quotientMatrix (fun i j => (M i j : ℝ)) hs := by
    funext i j
    simpa only [N, e, Equiv.apply_symm_apply] using
      FiniteFieldQuotientLanguage.quotientMatrix_real M hsK _ hs (fun _ _ => rfl)
        (e.symm i) (e.symm j)
  have hv : (fun i => (v i : ℝ)) =
      Twins.quotientWeight (fun i j => (M i j : ℝ)) (fun i => (w i : ℝ)) := by
    funext i
    simpa only [v, e, Equiv.apply_symm_apply] using
      FiniteFieldQuotientLanguage.quotientWeight_real M _ (fun _ _ => rfl) w (e.symm i)
  have hnv : Structures.WeightedClass (fun i j => (N i j : ℝ)) (fun i => (v i : ℝ)) := by
    rw [hN,hv]
    exact h
  have hf := weightedClass_inFP_of_ising hIsing K₀ basis N v hnv
  have hq := SurfaceWeightedBlockTractability.color_inFP basis e N v hf
  have hm : (fun i j => N (e i) (e j)) = Twins.quotientMatrix M hsK := by
    funext i j
    simp only [N, Equiv.symm_apply_apply]
  have hw : (fun i => v (e i)) = Twins.quotientWeight M w := by
    funext i
    simp only [v, Equiv.symm_apply_apply]
  rw [hm,hw] at hq
  apply hq.congr
  intro g
  exact (evaluate_homogeneous g.val.1 (graph_valid g.property) (Twins.quotientMatrix M hsK)
    (Twins.quotientWeight M w)).trans
    ((Twins.partition_canonicalQuotient (g.val.1.toMultiGraph (graph_valid g.property)) M w hsK).symm.trans
      (evaluate_homogeneous g.val.1 (graph_valid g.property) M w).symm)

end PlanarHom.SurfaceWeightedBlockTractability
