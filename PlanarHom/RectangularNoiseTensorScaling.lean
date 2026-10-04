import PlanarHom.RectangularPhysicalSourceForm
import PlanarHom.RectangularMixedPhysicalForms

/-! Exact scalar changes between Boolean noise and uniform Ising tensors,
including the literal mixed and parallel-square Gram matrices. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution

/-- The uniform Ising parameter corresponding to Boolean noise. -/
def noiseTensorParameter (ε : ℝ) : ℝ := (1-ε)/(1+ε)

/-- Scalar multiplying the normalized noise tensor in dimension `d`. -/
def noiseTensorScale (d : ℕ) (ε : ℝ) : ℝ := ((1+ε)/2)^d

theorem noiseTensorScale_pos (d : ℕ) {ε : ℝ} (hε : 0<ε) :
    0<noiseTensorScale d ε := by unfold noiseTensorScale; positivity

theorem noiseTensorParameter_range {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) :
    0<noiseTensorParameter ε ∧ noiseTensorParameter ε<1 := by
  have hd : 0<1+ε := by positivity
  constructor
  · exact div_pos (sub_pos.mpr hε1) hd
  · exact (div_lt_one hd).mpr (by linarith)

/-- Rational noise has a rational uniform Ising parameter. -/
def rationalNoiseTensorParameter (ε : ℚ) : ℚ := (1-ε)/(1+ε)

@[simp] theorem rationalNoiseTensorParameter_cast (ε : ℚ) :
    (rationalNoiseTensorParameter ε : ℝ)=noiseTensorParameter (ε:ℝ) := by
  simp [rationalNoiseTensorParameter,noiseTensorParameter]

theorem rationalNoiseTensorParameter_range {ε : ℚ} (hε : 0<ε) (hε1 : ε<1) :
    0<rationalNoiseTensorParameter ε ∧ rationalNoiseTensorParameter ε<1 := by
  have hd : 0<1+ε := by positivity
  constructor
  · exact div_pos (sub_pos.mpr hε1) hd
  · exact (div_lt_one hd).mpr (by linarith)

theorem bitNoise_eq_scaled_W {ε : ℝ} (hε : 1+ε≠0) (x y : Bool) :
    Boolean.bitNoise ε x y = ((1+ε)/2)*Boolean.W (noiseTensorParameter ε) x y := by
  by_cases hxy : x=y
  · simp [Boolean.bitNoise,Boolean.W,hxy]
  · simp only [Boolean.bitNoise,Boolean.W,hxy,if_false,noiseTensorParameter]
    field_simp

/-- Exact normalization, valid whenever the transformed parameter is defined. -/
theorem noiseMatrix_eq_smul_tensor {d : ℕ} {ε : ℝ} (hε : 1+ε≠0) :
    noiseMatrix (d:=d) ε = noiseTensorScale d ε •
      Boolean.tensor (fun _ : Fin d=>noiseTensorParameter ε) := by
  ext x y
  simp only [noiseMatrix,Boolean.noise,bitNoise_eq_scaled_W hε,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    noiseTensorScale,Boolean.tensor,Pi.smul_apply,smul_eq_mul]

theorem noiseMatrix_eq_smul_tensor_of_pos {d : ℕ} {ε : ℝ} (hε : 0<ε) :
    noiseMatrix (d:=d) ε = (((1+ε)/2)^d) •
      Boolean.tensor (fun _ : Fin d=>(1-ε)/(1+ε)) :=
  noiseMatrix_eq_smul_tensor (ne_of_gt (by linarith))

variable {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype X'] [Fintype Y'] [Fintype Z']

/-- Parallel square after applying an arbitrary left kernel. -/
def kernelParallelSquare (K : Matrix X X ℝ) (B : Matrix X Y ℝ) : Matrix X Y ℝ :=
  RectangularMixedGadgets.entrySquare (K*B)

def kernelParallelSquareGram (K : Matrix X X ℝ) (B : Matrix X Y ℝ) : Matrix X X ℝ :=
  kernelParallelSquare K B*(kernelParallelSquare K B).transpose

theorem kernelParallelSquare_smul (α : ℝ) (K : Matrix X X ℝ) (B : Matrix X Y ℝ) :
    kernelParallelSquare (α • K) B=α^2 • kernelParallelSquare K B := by
  unfold kernelParallelSquare
  rw [Matrix.smul_mul]
  ext i j
  change (α*(K*B) i j)^2=α^2*((K*B) i j)^2
  ring

theorem kernelParallelSquareGram_smul (α : ℝ) (K : Matrix X X ℝ) (B : Matrix X Y ℝ) :
    kernelParallelSquareGram (α • K) B=α^4 • kernelParallelSquareGram K B := by
  unfold kernelParallelSquareGram
  rw [kernelParallelSquare_smul,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul]
  simp only [smul_smul]
  congr 1
  ring

theorem mixed_kernel_smul (α : ℝ) (B : Matrix X Y ℝ) (K : Matrix Y Y ℝ) :
    B*(α • K)*B.transpose=α • (B*K*B.transpose) := by
  rw [Matrix.mul_smul,Matrix.smul_mul]

/-- Matrix multiplication commutes with compatible changes of both coordinates. -/
theorem reindex_mul (eX : X≃X') (eY : Y≃Y') (eZ : Z≃Z')
    (A : Matrix X Y ℝ) (B : Matrix Y Z ℝ) :
    Matrix.reindex eX eZ (A*B)=Matrix.reindex eX eY A*Matrix.reindex eY eZ B := by
  exact (Matrix.submatrix_mul_equiv A B eX.symm eY.symm eZ.symm).symm

theorem reindex_transpose (eX : X≃X') (eY : Y≃Y') (B : Matrix X Y ℝ) :
    Matrix.reindex eY eX B.transpose=(Matrix.reindex eX eY B).transpose := rfl

theorem reindex_kernelParallelSquare (eX : X≃X') (eY : Y≃Y')
    (K : Matrix X X ℝ) (B : Matrix X Y ℝ) :
    Matrix.reindex eX eY (kernelParallelSquare K B)=
      kernelParallelSquare (Matrix.reindex eX eX K) (Matrix.reindex eX eY B) := by
  unfold kernelParallelSquare
  have h := reindex_mul eX eX eY K B
  ext i j
  exact congrArg (fun M : Matrix X' Y' ℝ=>(M i j)^2) h

theorem reindex_kernelParallelSquareGram (eX : X≃X') (eY : Y≃Y')
    (K : Matrix X X ℝ) (B : Matrix X Y ℝ) :
    Matrix.reindex eX eX (kernelParallelSquareGram K B)=
      kernelParallelSquareGram (Matrix.reindex eX eX K) (Matrix.reindex eX eY B) := by
  unfold kernelParallelSquareGram
  rw [reindex_mul eX eY eX,reindex_transpose,reindex_kernelParallelSquare]

/-- The existing physical parallel square is the arbitrary-kernel construction
specialized to the Boolean noise matrix. -/
theorem parallelSquare_eq_kernelParallelSquare {a b : ℕ}
    (B : Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ) (ε : ℝ) :
    parallelSquare B ε=kernelParallelSquare (noiseMatrix ε) B := by
  ext x y
  exact (pow_two _).symm

theorem parallelSquareGram_eq_kernelParallelSquareGram {a b : ℕ}
    (B : Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ) (ε : ℝ) :
    parallelSquareGram B ε=kernelParallelSquareGram (noiseMatrix ε) B := by
  rw [parallelSquareGram,parallelSquare_eq_kernelParallelSquare]
  rfl

theorem parallelSquareGram_eq_scaled_tensorGram {a b : ℕ}
    (B : Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ) {ε : ℝ} (hε : 0<ε) :
    parallelSquareGram B ε=(noiseTensorScale a ε)^4 •
      kernelParallelSquareGram (Boolean.tensor (fun _ : Fin a=>noiseTensorParameter ε)) B := by
  rw [parallelSquareGram_eq_kernelParallelSquareGram,
    noiseMatrix_eq_smul_tensor (ne_of_gt (by linarith)),kernelParallelSquareGram_smul]

theorem mixed_noise_eq_scaled_tensor {a b : ℕ}
    (B : Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ) {ε : ℝ} (hε : 0<ε) :
    B*noiseMatrix ε*B.transpose=noiseTensorScale b ε •
      (B*tensorMatrix (fun _ : Fin b=>noiseTensorParameter ε)*B.transpose) := by
  rw [noiseMatrix_eq_smul_tensor (ne_of_gt (by linarith)),mixed_kernel_smul]
  rfl

end PlanarHom.RectangularWalshConvolution
