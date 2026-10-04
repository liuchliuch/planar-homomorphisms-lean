import PlanarHom.BooleanMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! NEW exact rectangular Walsh coordinates and noise programs. The transform
uses the existing unnormalized characters, with both inverse factors displayed.
All identities concern the original matrix entries. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {a b d:ℕ}

def inverseWalsh (d:ℕ) : Matrix (Cube d) (Cube d) ℝ := ((2:ℝ)^d)⁻¹ • walshMatrix d

theorem inverseWalsh_mul (d:ℕ) : inverseWalsh d*walshMatrix d=1 := by
  rw [inverseWalsh,Matrix.smul_mul,walshMatrix_mul_self,smul_smul]
  simp [pow_ne_zero d (by norm_num : (2:ℝ)≠0)]

theorem mul_inverseWalsh (d:ℕ) : walshMatrix d*inverseWalsh d=1 := by
  rw [inverseWalsh,Matrix.mul_smul,walshMatrix_mul_self,smul_smul]
  simp [pow_ne_zero d (by norm_num : (2:ℝ)≠0)]

def sourceCoefficients (B:Matrix (Cube a) (Cube b) ℝ) : Matrix (Cube a) (Cube b) ℝ :=
  inverseWalsh a*B*inverseWalsh b

def physicalValues (C:Matrix (Cube a) (Cube b) ℝ) : Matrix (Cube a) (Cube b) ℝ :=
  walshMatrix a*C*walshMatrix b

theorem source_inversion (B:Matrix (Cube a) (Cube b) ℝ) : physicalValues (sourceCoefficients B)=B := by
  unfold physicalValues sourceCoefficients
  calc
    _ = (walshMatrix a*inverseWalsh a)*B*(inverseWalsh b*walshMatrix b) := by simp only [Matrix.mul_assoc]
    _ = B := by rw [mul_inverseWalsh,inverseWalsh_mul,Matrix.one_mul,Matrix.mul_one]

theorem coefficients_inversion (C:Matrix (Cube a) (Cube b) ℝ) : sourceCoefficients (physicalValues C)=C := by
  unfold physicalValues sourceCoefficients
  calc
    _ = (inverseWalsh a*walshMatrix a)*C*(walshMatrix b*inverseWalsh b) := by simp only [Matrix.mul_assoc]
    _ = C := by rw [inverseWalsh_mul,mul_inverseWalsh,Matrix.one_mul,Matrix.mul_one]

def noiseMatrix (t:ℝ) : Matrix (Cube d) (Cube d) ℝ := Boolean.noise t

def noiseDiagonal (t:ℝ) : Matrix (Cube d) (Cube d) ℝ := Matrix.diagonal (fun S=>t^Boolean.degree S)

theorem noise_mul_walsh (t:ℝ) : noiseMatrix (d:=d) t*walshMatrix d=walshMatrix d*noiseDiagonal t := by
  ext x S
  simp only [Matrix.mul_apply,noiseMatrix,walshMatrix]
  simp_rw [character_symm _ S]
  rw [noise_character]
  simp [noiseDiagonal,Matrix.diagonal_apply,walshMatrix,character_symm,mul_comm]

def noiseValues (C:Matrix (Cube a) (Cube b) ℝ) (t:ℝ) : Matrix (Cube a) (Cube b) ℝ :=
  walshMatrix a*noiseDiagonal t*C*walshMatrix b

theorem noiseValues_eq (C:Matrix (Cube a) (Cube b) ℝ) (t:ℝ) :
    noiseValues C t=noiseMatrix t*physicalValues C := by
  rw [noiseValues,←noise_mul_walsh,physicalValues]
  simp only [Matrix.mul_assoc]

theorem source_noise_matrix (B:Matrix (Cube a) (Cube b) ℝ) (t:ℝ) :
    noiseValues (sourceCoefficients B) t=noiseMatrix t*B := by
  rw [noiseValues_eq,source_inversion]

def squaredNoise (C:Matrix (Cube a) (Cube b) ℝ) (t:ℝ) : Matrix (Cube a) (Cube b) ℝ :=
  fun x y=>noiseValues C t x y*noiseValues C t x y

def physicalGram (C:Matrix (Cube d) (Cube d) ℝ) (t:ℝ) : Matrix (Cube d) (Cube d) ℝ :=
  ((2:ℝ)^d)⁻¹^2 • (squaredNoise C t*(squaredNoise C t).transpose)

/-- Literal Fourier inversion expanded into the double character sum. -/
theorem physicalValues_apply (C:Matrix (Cube a) (Cube b) ℝ) (x:Cube a) (y:Cube b) :
    physicalValues C x y=∑S:Cube a,∑T:Cube b,C S T*character S x*character T y := by
  simp only [physicalValues,Matrix.mul_apply,walshMatrix,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  rw [character_symm x S]
  ring

/-- Noise multiplies the left Fourier degree by the exact monomial. -/
theorem noiseValues_apply (C:Matrix (Cube a) (Cube b) ℝ) (t:ℝ) (x:Cube a) (y:Cube b) :
    noiseValues C t x y=∑S:Cube a,∑T:Cube b,t^degree S*C S T*character S x*character T y := by
  have he:noiseValues C t=physicalValues (noiseDiagonal t*C):=by
    simp only [noiseValues,physicalValues,Matrix.mul_assoc]
  rw [he,physicalValues_apply]
  simp only [noiseDiagonal,Matrix.diagonal_mul]

end PlanarHom.RectangularWalshConvolution
