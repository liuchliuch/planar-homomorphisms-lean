/- Conditional assembly lemma. All explicit hypotheses remain visible;
the final closed endpoints instantiate the required foundations. -/
import PlanarHom.WeightedBlockTractabilityConditional
import PlanarHom.FiniteFieldQuotientLanguage

/-! Theorem 1.3's weighted easy direction after the actual identical-row
quotient. Classes keep the sum of the original vertex weights, including the
zero-row class. The program returns in the unchanged original field basis. -/
noncomputable section
open Classical
namespace PlanarHom.WeightedBlockTractability
open Complexity Complexity.MixedCode IsingTensorTractability
variable {C : Type} [Fintype C] {dimension : ℕ}

/-- Literal Theorem 1.3 structural sufficiency in any fixed original real
number field. Neither quotienting nor extension-field descent changes the
original raw input language or the prescribed output codec. -/
theorem positiveVertexWeightClass_inFP_of_ising (hIsing : BooleanTensorEasyAssembly.PositiveIsingFoundation) (K₀ : IntermediateField ℚ ℝ)
    [FiniteDimensional ℚ K₀] (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Matrix C C K₀) (w : C → K₀)
    (hs : ∀ i j, (M i j : ℝ) = (M j i : ℝ))
    (h : Structures.PositiveVertexWeightClass (fun i j => (M i j : ℝ))
      (fun i => (w i : ℝ)) hs) :
    (evaluationProblem basis (fun _ : Fin 1 => M) emptyUnaries w).InFP := by
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
  have hq := WeightedBlockTractability.color_inFP basis e N v hf
  have hm : (fun i j => N (e i) (e j)) = Twins.quotientMatrix M hsK := by
    funext i j
    simp only [N, Equiv.symm_apply_apply]
  have hw : (fun i => v (e i)) = Twins.quotientWeight M w := by
    funext i
    simp only [v, Equiv.symm_apply_apply]
  rw [hm,hw] at hq
  apply (evaluation_inFP_iff basis _ _ _).mpr
  apply ((evaluation_inFP_iff basis _ _ _).mp hq).congr
  intro g
  exact (evaluate_homogeneous g.val g.property.1 (Twins.quotientMatrix M hsK)
    (Twins.quotientWeight M w)).trans
    ((Twins.partition_canonicalQuotient (g.val.toMultiGraph g.property.1) M w hsK).symm.trans
      (evaluate_homogeneous g.val g.property.1 M w).symm)

end PlanarHom.WeightedBlockTractability

namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode IsingTensorTractability
variable {q : ℕ} (L : RealLanguage q 1 0)

/-- Main-body Theorem 1.3, easy implication, for the exact stated actual-row
quotient predicate and the unchanged original real-algebraic source problem. -/
theorem positive_vertex_weight_class_inFP_of_ising
    (hIsing : BooleanTensorEasyAssembly.PositiveIsingFoundation)
    (hs : ∀ i j, L.matrices 0 i j = L.matrices 0 j i)
    (h : Structures.PositiveVertexWeightClass (L.matrices 0) L.weights hs) :
    L.problem.InFP := by
  have hf := WeightedBlockTractability.positiveVertexWeightClass_inFP_of_ising hIsing L.field L.basis
    (L.matricesK 0) L.weightsK hs h
  have hM : L.matricesK = fun _ : Fin 1 => L.matricesK 0 := by
    funext l
    exact congrArg L.matricesK (Subsingleton.elim l 0)
  have hU : L.unariesK = (emptyUnaries : Fin 0 → Fin q → L.field) := by
    funext l
    exact Fin.elim0 l
  change (evaluationProblem L.basis L.matricesK L.unariesK L.weightsK).InFP
  rw [hM,hU]
  exact hf

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
