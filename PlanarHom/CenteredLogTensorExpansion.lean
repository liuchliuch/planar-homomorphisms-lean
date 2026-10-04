import PlanarHom.Boolean
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! NEW reconstructed literal entrywise-log expansion in coordinate Walsh
characters. All entries and parameters are real; no computational model is
asserted in this finite algebra module. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.CenteredLogTensorExpansion
open Boolean
variable {d:ℕ}

 def coordinateCharacter (r:Fin d) (x:Cube d) : ℝ := character (unitBit r) x
 def coordinateOuter (r:Fin d) : Matrix (Cube d) (Cube d) ℝ := fun x y=>coordinateCharacter r x*coordinateCharacter r y
 def ones (d:ℕ) : Matrix (Cube d) (Cube d) ℝ := fun _ _=>1
 def tensorLog (γ:ℝ) (ρ:Fin d→ℝ) : Matrix (Cube d) (Cube d) ℝ := fun x y=>Real.log (γ*tensor ρ x y)

 theorem coordinateCharacter_apply (r:Fin d) (x:Cube d) : coordinateCharacter r x=if x r then -1 else 1 := by
  rw [coordinateCharacter,character_symm,character_unitBit]

 theorem unitBit_eq_iff (r s:Fin d) : unitBit r=unitBit s ↔ r=s := by
  constructor
  · intro h
    have hh:=congrFun h r
    simpa [unitBit] using hh
  · rintro rfl
    rfl

 theorem coordinateCharacter_orthogonality (r s:Fin d) :
    (∑x:Cube d,coordinateCharacter r x*coordinateCharacter s x)=if r=s then (2:ℝ)^d else 0 := by
  simpa only [coordinateCharacter,unitBit_eq_iff] using character_orthogonality (unitBit r) (unitBit s)

 theorem coordinateCharacter_sum (r:Fin d) : (∑x:Cube d,coordinateCharacter r x)=0 := by
  have hn:unitBit r≠(fun _=>false):=by
    intro h
    have hh:=congrFun h r
    simp [unitBit] at hh
  simpa only [coordinateCharacter,character_zero,mul_one,if_neg hn] using
    character_orthogonality (unitBit r) (fun _=>false)

 theorem log_factor (ρ:ℝ) (r:Fin d) (x y:Cube d) :
    Real.log (W ρ (x r) (y r))=Real.log ρ/2+
      (-(Real.log ρ/2))*coordinateCharacter r x*coordinateCharacter r y := by
  rw [coordinateCharacter_apply,coordinateCharacter_apply]
  cases hx:x r <;> cases hy:y r <;> simp [W] <;> ring

 theorem tensorLog_expansion (γ:ℝ) (hγ:0<γ) (ρ:Fin d→ℝ) (hρ:∀r,0<ρ r) :
    tensorLog γ ρ=(Real.log γ+∑r,Real.log (ρ r)/2) • ones d+
      ∑r,(-(Real.log (ρ r)/2)) • coordinateOuter r := by
  ext x y
  simp only [tensorLog,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,ones,Matrix.sum_apply,coordinateOuter,mul_one]
  rw [Real.log_mul hγ.ne' (tensor_pos hρ x y).ne']
  rw [tensor,Real.log_prod Finset.univ (fun r=>W (ρ r) (x r) (y r)) (fun r _=>(W_pos (hρ r) (x r) (y r)).ne')]
  simp_rw [log_factor]
  rw [Finset.sum_add_distrib,←add_assoc]
  simp only [mul_assoc]

end PlanarHom.CenteredLogTensorExpansion
