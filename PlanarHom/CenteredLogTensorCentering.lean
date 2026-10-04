import PlanarHom.CenteredLogTensorExpansion

/-! NEW reconstructed exact centering of the ENTRYWISE tensor logarithm.
The all-ones component vanishes; every coordinate outer product is fixed by
both centering factors, including the empty tensor case. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.CenteredLogTensorExpansion
open Boolean
variable {d:ℕ}

 def centering (d:ℕ) : Matrix (Cube d) (Cube d) ℝ :=
  1-((2:ℝ)^d)⁻¹ • ones d

 theorem ones_mul_ones : ones d*ones d=(2:ℝ)^d • ones d := by
  ext x y
  simp [Matrix.mul_apply,ones,Cube,Fintype.card_fun]

 theorem ones_mul_coordinateOuter (r:Fin d) : ones d*coordinateOuter r=0 := by
  ext x y
  simp only [Matrix.mul_apply,ones,coordinateOuter,one_mul,Matrix.zero_apply]
  rw [←Finset.sum_mul,coordinateCharacter_sum,zero_mul]

 theorem coordinateOuter_mul_ones (r:Fin d) : coordinateOuter r*ones d=0 := by
  ext x y
  simp only [Matrix.mul_apply,ones,coordinateOuter,mul_one,Matrix.zero_apply]
  rw [←Finset.mul_sum,coordinateCharacter_sum,mul_zero]

 theorem centering_mul_ones : centering d*ones d=0 := by
  rw [centering,Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,ones_mul_ones,smul_smul]
  simp [pow_ne_zero d (by norm_num : (2:ℝ)≠0)]

 theorem ones_mul_centering : ones d*centering d=0 := by
  rw [centering,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul,ones_mul_ones,smul_smul]
  simp [pow_ne_zero d (by norm_num : (2:ℝ)≠0)]

 theorem centering_mul_coordinateOuter (r:Fin d) : centering d*coordinateOuter r=coordinateOuter r := by
  rw [centering,Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,ones_mul_coordinateOuter,smul_zero,sub_zero]

 theorem coordinateOuter_mul_centering (r:Fin d) : coordinateOuter r*centering d=coordinateOuter r := by
  rw [centering,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul,coordinateOuter_mul_ones,smul_zero,sub_zero]

 theorem centered_entrywise_log (γ:ℝ) (hγ:0<γ) (ρ:Fin d→ℝ) (hρ:∀r,0<ρ r) :
    centering d*tensorLog γ ρ*centering d=∑r,(-(Real.log (ρ r)/2)) • coordinateOuter r := by
  rw [tensorLog_expansion γ hγ ρ hρ,Matrix.mul_add,Matrix.mul_smul,centering_mul_ones,smul_zero,zero_add]
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Matrix.mul_smul,centering_mul_coordinateOuter,Matrix.smul_mul,coordinateOuter_mul_centering]

end PlanarHom.CenteredLogTensorExpansion
