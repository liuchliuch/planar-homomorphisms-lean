import PlanarHom.ThreeStatePositiveRank
import PlanarHom.CenteredLogStructuralForm
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Pure real spin-one Blume–Capel algebra, including the exact determinant
and obstruction for every positive vertex-weight vector. -/
noncomputable section
open Classical
namespace PlanarHom.BlumeCapel
open Structures

def spin : Fin 3→ℝ := ![-1,0,1]
def interaction (K:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := fun i j=>Real.exp (K*spin i*spin j)
def weight (D F:ℝ) (i:Fin 3) : ℝ := Real.exp (-D*(spin i)^2+F*spin i)

theorem symmetric (K:ℝ) (i j:Fin 3) : interaction K i j=interaction K j i := by
  unfold interaction; congr 1; ring

theorem positive (K:ℝ) (i j:Fin 3) : 0 < interaction K i j := Real.exp_pos _
theorem weight_positive (D F:ℝ) (i:Fin 3) : 0 < weight D F i := Real.exp_pos _

theorem spin_injective : Function.Injective spin := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [spin] at h

theorem rows_injective {K:ℝ} (hK:K≠0) : Function.Injective (interaction K) := by
  intro i j h
  have he:=congrFun h (2:Fin 3)
  change Real.exp (K*spin i*1)=Real.exp (K*spin j*1) at he
  simp only [mul_one,Real.exp_eq_exp] at he
  exact spin_injective (mul_left_cancel₀ hK he)

def rationalMatrix (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![x,1,x⁻¹;1,1,1;x⁻¹,1,x]

theorem interaction_eq (K:ℝ) : interaction K=rationalMatrix (Real.exp K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [interaction,spin,rationalMatrix,Real.exp_neg]

theorem rationalMatrix_det {x:ℝ} (hx:x≠0) :
    (rationalMatrix x).det=(x-1)^3*(x+1)/x^2 := by
  rw [rationalMatrix,Matrix.det_fin_three]
  change x*1*x- x*1*1-1*1*x+1*1*x⁻¹+x⁻¹*1*1-x⁻¹*1*x⁻¹=(x-1)^3*(x+1)/x^2
  field_simp [hx]
  <;> ring

theorem determinant (K:ℝ) :
    (interaction K).det=(Real.exp K-1)^3*(Real.exp K+1)/(Real.exp K)^2 := by
  rw [interaction_eq]
  exact rationalMatrix_det (Real.exp_ne_zero K)

theorem det_ne_zero {K:ℝ} (hK:K≠0) : (interaction K).det≠0 := by
  rw [determinant]
  apply div_ne_zero
  · apply mul_ne_zero
    · apply pow_ne_zero
      intro he
      have he':Real.exp K=1:=sub_eq_zero.mp he
      exact hK (Real.exp_injective (by simpa only [Real.exp_zero] using he'))
    · exact ne_of_gt (by linarith [Real.exp_pos K])
  · exact pow_ne_zero _ (Real.exp_ne_zero K)

theorem rank_three {K:ℝ} (hK:K≠0) : (interaction K).rank=3 := by
  have hi:IsUnit (interaction K) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (det_ne_zero hK))
  simpa using Matrix.rank_of_isUnit (interaction K) hi

theorem not_weighted_class {K:ℝ} (hK:K≠0) (w:Fin 3→ℝ) :
    ¬PositiveVertexWeightClass (interaction K) w (symmetric K) := by
  intro h
  have hu := (CenteredLogStructural.weightedClass_of_actual_membership
    (interaction K) w (symmetric K) (rows_injective hK) h).unweighted
  have hr := ThreeStateDimension.positive_nonnegativeClass_rank_le_one (positive K) hu
  rw [rank_three hK] at hr
  omega

theorem zero_interaction : interaction 0=fun _ _=>1 := by
  ext i j; simp [interaction]

end PlanarHom.BlumeCapel
