import PlanarHom.TractableBlockComposition
import PlanarHom.BooleanTensorEasyAssembly
import PlanarHom.AlgebraicProductInterpolation

/-! NEW actual rank-one/tensor source algorithm with only primitive positive
zero-field Ising FP explicit. Displayed parameters are derived algebraic from
source entries, computed in a finite compositum, and descended to the original
prescribed basis. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.TractableBlockComposition
open Complexity Complexity.MixedCode AlgebraicProductInterpolation
open BooleanTensorFPClosure BooleanTensorEasyAssembly
variable {C : Type} [Fintype C] {dimension k d : ℕ}

theorem source_rankOne_ising_tensor_inFP_of_ising (hIsing : PositiveIsingFoundation)
    (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (basis : Module.Basis (Fin dimension) ℚ K₀) (M : Matrix C C K₀)
    (i0 : Fin k) (e : C ≃ Fin k × Boolean.Cube d)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (ρ : Fin d → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hsource : Matrix.reindex e e (fun i j => (M i j : ℝ)) =
      fun p r => a p.1 * a r.1 * Boolean.tensor ρ p.2 r.2) :
    (evaluationProblem basis (fun _ : Fin 1 => M) emptyUnaries (fun _ => 1)).InFP := by
  let z : Boolean.Cube d := fun _ => false
  have he (p r : Fin k × Boolean.Cube d) :
      (M (e.symm p) (e.symm r) : ℝ) = a p.1 * a r.1 * Boolean.tensor ρ p.2 r.2 :=
    congrArg (fun A : Matrix (Fin k × Boolean.Cube d) (Fin k × Boolean.Cube d) ℝ => A p r) hsource
  have hmalg (i j : C) : IsAlgebraic ℚ (M i j : ℝ) :=
    (IsAlgebraic.of_finite ℚ (M i j)).algHom K₀.val
  have haalg : ∀ i, IsAlgebraic ℚ (a i) := by
    intro i
    apply IsAlgebraic.of_pow (n := 2) (by norm_num)
    simpa only [he, Boolean.tensor_diag, mul_one, pow_two] using
      hmalg (e.symm (i,z)) (e.symm (i,z))
  have hralg : ∀ i, IsAlgebraic ℚ (ρ i) := by
    intro i
    have heq : ρ i = (M (e.symm (i0,z)) (e.symm (i0,Boolean.unitBit i)) : ℝ) /
        (M (e.symm (i0,z)) (e.symm (i0,z)) : ℝ) := by
      rw [he,he]
      simp only [z, Boolean.tensor_unitBit, Boolean.tensor_diag, mul_one]
      field_simp [ne_of_gt (ha i0)]
    rw [heq,div_eq_mul_inv]
    exact (hmalg _ _).mul (hmalg _ _).inv
  let constants : Fin k ⊕ Fin d → ℝ := Sum.elim a ρ
  have hc : ∀ p, IsAlgebraic ℚ (constants p) := by
    rintro (i | i)
    · exact haalg i
    · exact hralg i
  let E := extensionField K₀ constants
  letI : FiniteDimensional ℚ E := extension_finiteDimensional K₀ constants hc
  let φ := sourceInclusion K₀ constants
  let bE := extensionBasis K₀ constants hc
  let aE : Fin k → E := fun i => targetValue K₀ constants (.inl i)
  let ρE : Fin d → E := fun i => targetValue K₀ constants (.inr i)
  let B : Matrix (Fin k × Boolean.Cube d) (Fin k × Boolean.Cube d) E :=
    MultiGraph.tensorInteraction (fun i j => aE i * aE j)
      (BooleanTensorSpectral.tensor (fun i => isingMatrix (ρE i)))
  have hB : (evaluationProblem bE (fun _ : Fin 1 => B) emptyUnaries (fun _ => 1)).InFP :=
    product_inFP bE _ _ (RankOneEvaluationMachine.evaluation_inFP bE aE (fun _ => 1))
      (tensor_inFP bE (fun i => isingMatrix (ρE i))
        (fun i => hIsing E _ bE (ρE i) (hρ i)))
  have hfp := color_inFP bE e B hB
  have hm : (fun i j => φ (M i j)) = fun i j => B (e i) (e j) := by
    funext i j
    apply Subtype.ext
    have h := he (e i) (e j)
    simpa [B, MultiGraph.tensorInteraction, BooleanTensorSpectral.tensor,
      Boolean.tensor, isingMatrix, Boolean.W, aE, ρE, constants, map_prod, apply_ite] using h
  apply field_descent_inFP basis bE φ M
  have hfamily : (fun _ : Fin 1 => fun i j => φ (M i j)) =
      fun _ : Fin 1 => fun i j => B (e i) (e j) := funext (fun _ => hm)
  rw [hfamily]
  exact hfp

end PlanarHom.TractableBlockComposition
