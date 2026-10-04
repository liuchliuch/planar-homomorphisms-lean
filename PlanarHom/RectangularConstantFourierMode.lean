import PlanarHom.RectangularPerronNormalization
import PlanarHom.RectangularWalshGram

/-! NEW actual constant Fourier mode of a positive square source matrix whose
two Grams are Boolean tensors. The scalar comes from its literal row sum. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

theorem sourceCoefficients_apply (B:Matrix (Cube d) (Cube d) ℝ) (S T:Cube d):
    sourceCoefficients B S T=((2:ℝ)^d)⁻¹^2*
      (∑x:Cube d,∑y:Cube d,B x y*character S x*character T y):=by
  simp only [sourceCoefficients,inverseWalsh,Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.smul_apply,smul_eq_mul]
  rw [←mul_assoc,←pow_two]
  congr 1
  simp only [Matrix.mul_apply,walshMatrix,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [character_symm y T]
  ring

theorem character_sum (T:Cube d):
    (∑y:Cube d,character T y)=if T=(fun _=>false) then (2:ℝ)^d else 0:=by
  simpa only [character_zero,mul_one] using character_orthogonality T (fun _=>false)

theorem coefficient_zero_row (B:Matrix (Cube d) (Cube d) ℝ) (s0:ℝ)
    (hcol:∀j,rowSum B.transpose j=s0) (T:Cube d):
    sourceCoefficients B (fun _=>false) T=if T=(fun _=>false) then s0/((2:ℝ)^d) else 0:=by
  rw [sourceCoefficients_apply]
  simp only [character_zero,mul_one]
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_mul]
  have hc:∀y,(∑x,B x y)=s0:=hcol
  simp_rw [hc]
  rw [←Finset.mul_sum,character_sum]
  split_ifs <;> field_simp <;> ring

theorem coefficient_zero_column (B:Matrix (Cube d) (Cube d) ℝ) (s0:ℝ)
    (hrow:∀i,rowSum B i=s0) (S:Cube d):
    sourceCoefficients B S (fun _=>false)=if S=(fun _=>false) then s0/((2:ℝ)^d) else 0:=by
  rw [sourceCoefficients_apply]
  simp only [character_zero,mul_one]
  simp_rw [←Finset.sum_mul]
  have hr:∀x,(∑y,B x y)=s0:=hrow
  simp_rw [hr]
  rw [←Finset.mul_sum,character_sum]
  split_ifs <;> field_simp <;> ring

def normalizedCoefficients (B:Matrix (Cube d) (Cube d) ℝ) (s0:ℝ):Matrix (Cube d) (Cube d) ℝ:=
  ((2:ℝ)^d/s0) • sourceCoefficients B

theorem normalized_zero_row (B:Matrix (Cube d) (Cube d) ℝ) (s0:ℝ) (hs0:s0≠0)
    (hcol:∀j,rowSum B.transpose j=s0) (T:Cube d):
    normalizedCoefficients B s0 (fun _=>false) T=if T=(fun _=>false) then 1 else 0:=by
  rw [normalizedCoefficients,Matrix.smul_apply,smul_eq_mul,coefficient_zero_row B s0 hcol]
  split_ifs <;> field_simp <;> ring

theorem normalized_zero_column (B:Matrix (Cube d) (Cube d) ℝ) (s0:ℝ) (hs0:s0≠0)
    (hrow:∀i,rowSum B i=s0) (S:Cube d):
    normalizedCoefficients B s0 S (fun _=>false)=if S=(fun _=>false) then 1 else 0:=by
  rw [normalizedCoefficients,Matrix.smul_apply,smul_eq_mul,coefficient_zero_column B s0 hrow]
  split_ifs <;> field_simp <;> ring

theorem exists_normalized_constant_mode (B:Matrix (Cube d) (Cube d) ℝ) (hB:∀i j,0<B i j)
    (γX γY:ℝ) (ρX ρY:Fin d→ℝ)
    (hX:∀i j,(B*B.transpose) i j=γX*Boolean.tensor ρX i j)
    (hY:∀i j,(B.transpose*B) i j=γY*Boolean.tensor ρY i j):
    ∃s0:ℝ,0<s0 ∧ (∀i,rowSum B i=s0) ∧ (∀i,rowSum B.transpose i=s0) ∧
      (∀T,normalizedCoefficients B s0 (fun _=>false) T=if T=(fun _=>false) then 1 else 0) ∧
      (∀S,normalizedCoefficients B s0 S (fun _=>false)=if S=(fun _=>false) then 1 else 0):=by
  have hx:∀i,rowSum (B*B.transpose) i=γX*(∏ r : Fin d, (1+ρX r)):=by
    intro i
    simp only [rowSum,hX,←Finset.mul_sum,tensor_row_sum]
  have hy:∀i,rowSum (B.transpose*B) i=γY*(∏ r : Fin d, (1+ρY r)):=by
    intro i
    simp only [rowSum,hY,←Finset.mul_sum,tensor_row_sum]
  obtain ⟨s0,hs0,hr,hc,_,_⟩:=gram_constant_mode B hB _ _ hx hy
  exact ⟨s0,hs0,hr,hc,normalized_zero_row B s0 hs0.ne' hc,normalized_zero_column B s0 hs0.ne' hr⟩

end PlanarHom.RectangularWalshConvolution
