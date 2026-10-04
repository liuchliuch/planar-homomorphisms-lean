import PlanarHom.RectangularConstantFourierMode

/-! NEW exact normalized Fourier Gram equations for the original source and
its genuine mixed-noise gadget. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

theorem physicalValues_mixedNoise (C:Matrix (Cube d) (Cube d) ℝ) (z:ℝ):
    physicalValues C*noiseMatrix z*(physicalValues C).transpose=
      (2:ℝ)^d • physicalValues (C*noiseDiagonal z*C.transpose):=by
  rw [physicalValues_transpose]
  unfold physicalValues
  have hn:walshMatrix d*noiseMatrix z*walshMatrix d=(2:ℝ)^d • noiseDiagonal z:=by
    rw [Matrix.mul_assoc,noise_mul_walsh,←Matrix.mul_assoc,walshMatrix_mul_self,Matrix.smul_mul,Matrix.one_mul]
  calc
    _ = walshMatrix d*C*(walshMatrix d*noiseMatrix z*walshMatrix d)*C.transpose*walshMatrix d:=by
      simp only [Matrix.mul_assoc]
    _ = _:=by rw [hn];simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]

theorem sourceCoefficients_mixedNoise (B:Matrix (Cube d) (Cube d) ℝ) (z:ℝ):
    sourceCoefficients (B*noiseMatrix z*B.transpose)=
      (2:ℝ)^d • (sourceCoefficients B*noiseDiagonal z*(sourceCoefficients B).transpose):=by
  have h:=physicalValues_mixedNoise (sourceCoefficients B) z
  rw [source_inversion] at h
  rw [h,sourceCoefficients_smul,coefficients_inversion]

theorem normalized_gram (B:Matrix (Cube d) (Cube d) ℝ) (s0:ℝ) (hs0:s0≠0)
    (γ:ℝ) (ρ:Fin d→ℝ) (h:B*B.transpose=γ • Boolean.tensor ρ):
    normalizedCoefficients B s0*(normalizedCoefficients B s0).transpose=
      (γ/s0^2) • Matrix.diagonal (eigenvalue ρ):=by
  let n:ℝ:=(2:ℝ)^d
  have hn:n≠0:=pow_ne_zero d (by norm_num)
  have he:=congrArg sourceCoefficients h
  rw [sourceCoefficients_gram,tensor_coefficients] at he
  have hp:sourceCoefficients B*(sourceCoefficients B).transpose=
      (γ/n^2) • Matrix.diagonal (eigenvalue ρ):=by
    apply (smul_right_injective _ hn)
    dsimp only
    rw [smul_smul]
    change n • (sourceCoefficients B*(sourceCoefficients B).transpose)=_
    rw [he]
    congr 1
    field_simp [n] <;> rfl
  rw [normalizedCoefficients,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hp,smul_smul]
  congr 1
  change (n/s0*(n/s0))*(γ/n^2)=γ/s0^2
  field_simp [n] <;> rfl

theorem normalized_mixedGram (B:Matrix (Cube d) (Cube d) ℝ) (s0:ℝ) (hs0:s0≠0)
    (z γ:ℝ) (ρ:Fin d→ℝ) (h:B*noiseMatrix z*B.transpose=γ • Boolean.tensor ρ):
    normalizedCoefficients B s0*noiseDiagonal z*(normalizedCoefficients B s0).transpose=
      (γ/s0^2) • Matrix.diagonal (eigenvalue ρ):=by
  let n:ℝ:=(2:ℝ)^d
  have hn:n≠0:=pow_ne_zero d (by norm_num)
  have he:=congrArg sourceCoefficients h
  rw [sourceCoefficients_mixedNoise,tensor_coefficients] at he
  have hp:sourceCoefficients B*noiseDiagonal z*(sourceCoefficients B).transpose=
      (γ/n^2) • Matrix.diagonal (eigenvalue ρ):=by
    apply (smul_right_injective _ hn)
    dsimp only
    rw [smul_smul]
    change n • (sourceCoefficients B*noiseDiagonal z*(sourceCoefficients B).transpose)=_
    rw [he]
    congr 1
    field_simp [n] <;> rfl
  simp only [normalizedCoefficients,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [hp,smul_smul]
  congr 1
  change (n/s0*(n/s0))*(γ/n^2)=γ/s0^2
  field_simp [n] <;> rfl

/-- Row normalization by actual nonzero lengths produces a genuine orthogonal
matrix, without assuming the source coefficient matrix is already orthogonal. -/
theorem rowNormalize_orthogonal {I:Type} [Fintype I] [DecidableEq I]
    (C:Matrix I I ℝ) (θ:I→ℝ) (hθ:∀i,θ i≠0)
    (hC:C*C.transpose=Matrix.diagonal (fun i=>θ i^2)):
    (Matrix.diagonal (fun i=>(θ i)⁻¹)*C)*
      (Matrix.diagonal (fun i=>(θ i)⁻¹)*C).transpose=1:=by
  rw [Matrix.transpose_mul,Matrix.diagonal_transpose]
  calc
    _ = Matrix.diagonal (fun i=>(θ i)⁻¹)*(C*C.transpose)*Matrix.diagonal (fun i=>(θ i)⁻¹):=by
      simp only [Matrix.mul_assoc]
    _ = 1:=by
      rw [hC,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
      ext i j
      simp only [Matrix.diagonal_apply,Matrix.one_apply]
      split_ifs <;> simp [hθ,pow_two]

end PlanarHom.RectangularWalshConvolution
