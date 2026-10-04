import PlanarHom.WeightedBlockFPClosure
import PlanarHom.BooleanTensorEasyAssembly
import PlanarHom.AlgebraicProductInterpolation

/-! NEW actual weighted rank-one/tensor source algorithm with only primitive positive
zero-field Ising FP explicit. Displayed parameters are derived algebraic from
source entries, computed in a finite compositum, and descended to the original
prescribed basis. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.WeightedBlockTractability
open Complexity Complexity.MixedCode AlgebraicProductInterpolation
open BooleanTensorEasyAssembly
variable {C : Type} [Fintype C] {dimension k d : ℕ}

theorem source_positive_block_inFP_of_ising (hIsing : PositiveIsingFoundation)
    (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (basis : Module.Basis (Fin dimension) ℚ K₀) (M : Matrix C C K₀) (w : C → K₀)
    (i0 : Fin k) (e : C ≃ Fin k × Boolean.Cube d)
    (a mass : Fin k → ℝ) (ha : ∀ i, 0 < a i) (ρ : Fin d → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hsource : Matrix.reindex e e (fun i j => (M i j : ℝ)) =
      fun p r => a p.1 * a r.1 * Boolean.tensor ρ p.2 r.2)
    (hweight : ∀i,(w i:ℝ)=mass (e i).1) :
    (evaluationProblem basis (fun _ : Fin 1 => M) (fun u:Fin 0=>u.elim0) w).InFP := by
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
  have hmassalg : ∀i,IsAlgebraic ℚ (mass i) := by
    intro i
    have h := (IsAlgebraic.of_finite ℚ (w (e.symm (i,z)))).algHom K₀.val
    change IsAlgebraic ℚ (w (e.symm (i,z)):ℝ) at h
    simpa only [hweight,Equiv.apply_symm_apply] using h
  let constants : (Fin k ⊕ Fin k) ⊕ Fin d → ℝ := Sum.elim (Sum.elim a mass) ρ
  have hc : ∀ p, IsAlgebraic ℚ (constants p) := by
    rintro ((i | i) | i)
    · exact haalg i
    · exact hmassalg i
    · exact hralg i
  let E := extensionField K₀ constants
  letI : FiniteDimensional ℚ E := extension_finiteDimensional K₀ constants hc
  let φ := sourceInclusion K₀ constants
  let bE := extensionBasis K₀ constants hc
  let aE : Fin k → E := fun i => targetValue K₀ constants (.inl (.inl i))
  let massE : Fin k → E := fun i=>targetValue K₀ constants (.inl (.inr i))
  let ρE : Fin d → E := fun i => targetValue K₀ constants (.inr i)
  let B : Matrix (Fin k × Boolean.Cube d) (Fin k × Boolean.Cube d) E :=
    MultiGraph.tensorInteraction (fun i j => aE i * aE j)
      (BooleanTensorSpectral.tensor (fun i => isingMatrix (ρE i)))
  have hB : (evaluationProblem bE (fun _ : Fin 1 => B) (fun u:Fin 0=>u.elim0)
      (fun p=>massE p.1)).InFP := by
    have h := product_inFP bE (fun i j=>aE i*aE j)
      (BooleanTensorSpectral.tensor (fun i=>isingMatrix (ρE i))) massE (fun _=>1)
      (RankOneEvaluationMachine.evaluation_inFP bE aE massE)
      (BooleanTensorFPClosure.tensor_inFP bE (fun i=>isingMatrix (ρE i))
        (fun i=>hIsing E _ bE (ρE i) (hρ i)))
    have hw1 : MultiGraph.tensorVertexWeight massE (fun _:Boolean.Cube d=>(1:E)) =
        (fun p : Fin k × Boolean.Cube d=>massE p.1) := by
      funext p
      exact mul_one _
    rw [hw1] at h
    exact h
  have hfp := color_inFP bE e B (fun p=>massE p.1) hB
  have hm : (fun i j => φ (M i j)) = fun i j => B (e i) (e j) := by
    funext i j
    apply Subtype.ext
    have h := he (e i) (e j)
    simpa [B, MultiGraph.tensorInteraction, BooleanTensorSpectral.tensor,
      Boolean.tensor, isingMatrix, Boolean.W, aE, ρE, constants, map_prod, apply_ite] using h
  have hw : (fun i=>φ (w i))=(fun i=>massE (e i).1) := by
    funext i
    exact Subtype.ext (hweight i)
  apply field_descent_inFP basis bE φ M w
  have hfamily : (fun _ : Fin 1 => fun i j => φ (M i j)) =
      fun _ : Fin 1 => fun i j => B (e i) (e j) := funext (fun _ => hm)
  rw [hfamily,hw]
  exact hfp

end PlanarHom.WeightedBlockTractability
