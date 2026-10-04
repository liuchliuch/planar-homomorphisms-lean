import PlanarHom.RectangularWalshConvolution

/-! NEW literal Fourier Gram formulas for physical parallel squaring. The
normalization constants come from exact unnormalized Walsh orthogonality. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {a b d:ℕ}

theorem physicalValues_transpose (C:Matrix (Cube a) (Cube b) ℝ):
    (physicalValues C).transpose=physicalValues C.transpose:=by
  simp only [physicalValues,Matrix.transpose_mul,walshMatrix_symm,Matrix.mul_assoc]

theorem physicalValues_smul (c:ℝ) (C:Matrix (Cube a) (Cube b) ℝ):
    physicalValues (c • C)=c • physicalValues C:=by
  simp only [physicalValues,Matrix.mul_smul,Matrix.smul_mul]

theorem sourceCoefficients_smul (c:ℝ) (B:Matrix (Cube a) (Cube b) ℝ):
    sourceCoefficients (c • B)=c • sourceCoefficients B:=by
  simp only [sourceCoefficients,Matrix.mul_smul,Matrix.smul_mul]

theorem physicalValues_gram (C:Matrix (Cube a) (Cube b) ℝ):
    physicalValues C*(physicalValues C).transpose=(2:ℝ)^b • physicalValues (C*C.transpose):=by
  rw [physicalValues_transpose]
  unfold physicalValues
  calc
    _ = walshMatrix a*C*(walshMatrix b*walshMatrix b)*C.transpose*walshMatrix a:=by
      simp only [Matrix.mul_assoc]
    _ = _:=by
      rw [walshMatrix_mul_self,Matrix.mul_smul,Matrix.mul_one]
      simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc]

theorem sourceCoefficients_gram (B:Matrix (Cube a) (Cube b) ℝ):
    sourceCoefficients (B*B.transpose)=(2:ℝ)^b • (sourceCoefficients B*(sourceCoefficients B).transpose):=by
  have h:=physicalValues_gram (sourceCoefficients B)
  rw [source_inversion] at h
  rw [h,sourceCoefficients_smul,coefficients_inversion]

theorem physicalGram_coefficients (C:Matrix (Cube d) (Cube d) ℝ) (t:ℝ):
    sourceCoefficients (physicalGram C t)=((2:ℝ)^d)⁻¹ •
      (coefficientConvolution (noisyCoefficients C t) (noisyCoefficients C t)*
       (coefficientConvolution (noisyCoefficients C t) (noisyCoefficients C t)).transpose):=by
  rw [physicalGram,sourceCoefficients_smul,sourceCoefficients_gram,squaredNoise_coefficients,smul_smul]
  congr 1
  field_simp

theorem tensor_coefficients (γ:ℝ) (ρ:Fin d→ℝ):
    sourceCoefficients (γ • Boolean.tensor ρ)= (γ*((2:ℝ)^d)⁻¹) • Matrix.diagonal (eigenvalue ρ):=by
  rw [sourceCoefficients_smul]
  unfold sourceCoefficients inverseWalsh
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have he:walshMatrix d*Matrix.of (Boolean.tensor ρ)*walshMatrix d=
      (2:ℝ)^d • Matrix.diagonal (eigenvalue ρ):=by
    rw [Matrix.mul_assoc,tensor_mul_walshMatrix,←Matrix.mul_assoc,walshMatrix_mul_self,Matrix.smul_mul,Matrix.one_mul]
  change (γ*(((2:ℝ)^d)⁻¹*((2:ℝ)^d)⁻¹)) •
    (walshMatrix d*Matrix.of (Boolean.tensor ρ)*walshMatrix d)=
    (γ*((2:ℝ)^d)⁻¹) • Matrix.diagonal (eigenvalue ρ)
  rw [he,smul_smul]
  congr 1
  field_simp

/-- Actual zero-field tensor form of the physical Gram gives the literal
squared Fourier row norms and vanishing off-diagonal correlations. -/
theorem convolution_gram_of_tensor (C:Matrix (Cube d) (Cube d) ℝ) (t γ:ℝ) (ρ:Fin d→ℝ)
    (h:physicalGram C t=γ • Boolean.tensor ρ):
    coefficientConvolution (noisyCoefficients C t) (noisyCoefficients C t)*
      (coefficientConvolution (noisyCoefficients C t) (noisyCoefficients C t)).transpose=
      γ • Matrix.diagonal (eigenvalue ρ):=by
  have he:=congrArg sourceCoefficients h
  rw [physicalGram_coefficients,tensor_coefficients,show γ*((2:ℝ)^d)⁻¹=((2:ℝ)^d)⁻¹*γ by ring,←smul_smul] at he
  exact (smul_right_injective _ (inv_ne_zero (pow_ne_zero d (by norm_num : (2:ℝ)≠0)))) he

end PlanarHom.RectangularWalshConvolution
