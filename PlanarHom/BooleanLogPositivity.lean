import PlanarHom.PositiveExponentialEntries
import PlanarHom.KernelContinuation
import PlanarHom.CubeLocalBlocks
import PlanarHom.CubeGraphMetric

/-!
# Positive logarithmic edges of positive definite Boolean tensors

The proof uses the genuine exponential power series and the spectral inverse
identities, rather than assuming an explicit formula for the two eigenvalues.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.BooleanLogPositivity

/-- A signed nonnegative two-by-two matrix has nonnegative diagonal and
nonpositive off-diagonal. In dimension two this cone is multiplicatively closed. -/
def SignedNonnegative (A : Matrix Bool Bool ℝ) : Prop :=
  0 ≤ A false false ∧ A false true ≤ 0 ∧ A true false ≤ 0 ∧ 0 ≤ A true true

theorem signedNonnegative_one : SignedNonnegative (1 : Matrix Bool Bool ℝ) := by
  simp [SignedNonnegative]

theorem SignedNonnegative.mul {A B : Matrix Bool Bool ℝ}
    (hA : SignedNonnegative A) (hB : SignedNonnegative B) : SignedNonnegative (A * B) := by
  rcases hA with ⟨hA00, hA01, hA10, hA11⟩
  rcases hB with ⟨hB00, hB01, hB10, hB11⟩
  simp only [SignedNonnegative, Matrix.mul_apply, Fintype.sum_bool]
  exact ⟨add_nonneg (mul_nonneg_of_nonpos_of_nonpos hA01 hB10) (mul_nonneg hA00 hB00),
    add_nonpos (mul_nonpos_of_nonpos_of_nonneg hA01 hB11) (mul_nonpos_of_nonneg_of_nonpos hA00 hB01),
    add_nonpos (mul_nonpos_of_nonneg_of_nonpos hA11 hB10) (mul_nonpos_of_nonpos_of_nonneg hA10 hB00),
    add_nonneg (mul_nonneg hA11 hB11) (mul_nonneg_of_nonpos_of_nonpos hA10 hB01)⟩

theorem SignedNonnegative.pow {A : Matrix Bool Bool ℝ} (hA : SignedNonnegative A)
    (n : ℕ) : SignedNonnegative (A ^ n) := by
  induction n with
  | zero => simpa using signedNonnegative_one
  | succ n ih => rw [pow_succ]; exact ih.mul hA

/-- The genuine exponential preserves nonpositive off-diagonal entries in two
states, with no restriction on the diagonal. -/
theorem exp_offDiagonal_nonpos (A : Matrix Bool Bool ℝ)
    (h01 : A false true ≤ 0) (h10 : A true false ≤ 0) :
    NormedSpace.exp ℝ A false true ≤ 0 := by
  obtain ⟨c, _, hc⟩ := MatrixLogCoefficients.exists_nonneg_diagonal_shift A
  let B : Matrix Bool Bool ℝ := A + c • 1
  have hB : SignedNonnegative B := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [B] using hc false
    · simpa [B] using h01
    · simpa [B] using h10
    · simpa [B] using hc true
  have hsum : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * (B ^ n) false true)
      (NormedSpace.exp ℝ B false true) := by
    simpa only [MatrixLogCoefficients.entryCLM_apply, map_smul, smul_eq_mul] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) B).mapL
        (MatrixLogCoefficients.entryCLM false true)
  have hle : NormedSpace.exp ℝ B false true ≤ 0 := by
    rw [← hsum.tsum_eq]
    exact tsum_nonpos (fun n => mul_nonpos_of_nonneg_of_nonpos (by positivity) (hB.pow n).2.1)
  have hshift := congrArg (fun M : Matrix Bool Bool ℝ => M false true)
    (TraceExponential.exp_add_smul_one A c)
  change NormedSpace.exp ℝ B false true = Real.exp c * NormedSpace.exp ℝ A false true at hshift
  rw [hshift] at hle
  nlinarith [Real.exp_pos c]

/-- A positive-definite real two-by-two matrix with positive off-diagonal has
strictly positive off-diagonal in its actual spectral logarithm. -/
theorem matrixLog_offDiagonal_pos {N : Matrix Bool Bool ℝ} (hN : N.PosDef)
    (hv : 0 < N false true) : 0 < EntropyCompletion.matrixLog N false true := by
  by_contra h
  have h01 : EntropyCompletion.matrixLog N false true ≤ 0 := le_of_not_gt h
  have hh : (EntropyCompletion.matrixLog N).IsHermitian := IsSelfAdjoint.log
  have he : EntropyCompletion.matrixLog N true false = EntropyCompletion.matrixLog N false true := by
    simpa only [star_trivial] using hh.apply false true
  have hle := exp_offDiagonal_nonpos (EntropyCompletion.matrixLog N) h01 (he ▸ h01)
  rw [KernelContinuation.exp_matrixLog hN] at hle
  exact (not_le_of_gt hv) hle


open CubeTensorExponential

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate lifting preserves real symmetry. -/
theorem coordinateLift_isHermitian (r : ι) {A : Matrix Bool Bool ℝ}
    (hA : A.IsHermitian) : (coordinateLift r A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro z w
  simp only [coordinateLift, star_trivial]
  rw [show A (w r) (z r) = A (z r) (w r) from hA.apply (z r) (w r)]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  simp [Matrix.one_apply, eq_comm]

/-- The true sum of coordinate-local spectral logarithms. -/
def tensorLog (A : ι → Matrix Bool Bool ℝ) : Matrix (ι → Bool) (ι → Bool) ℝ :=
  ∑ r, coordinateLift r (EntropyCompletion.matrixLog (A r))

theorem tensorLog_isHermitian (A : ι → Matrix Bool Bool ℝ) : (tensorLog A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro z w
  simp only [tensorLog, Matrix.sum_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro r _
  exact (coordinateLift_isHermitian r (show (EntropyCompletion.matrixLog (A r)).IsHermitian
    from IsSelfAdjoint.log)).apply z w

/-- Exponentiating the coordinate-local logarithms gives the literal tensor. -/
theorem exp_tensorLog (A : ι → Matrix Bool Bool ℝ) (hA : ∀ r, (A r).PosDef) :
    NormedSpace.exp ℝ (tensorLog A) = tensor A := by
  unfold tensorLog
  rw [exp_sum_coordinateLift_eq_tensor]
  congr 1
  funext r
  exact KernelContinuation.exp_matrixLog (hA r)

/-- A tensor of positive-definite real Boolean factors is positive definite. -/
theorem tensor_posDef (A : ι → Matrix Bool Bool ℝ) (hA : ∀ r, (A r).PosDef) :
    (tensor A).PosDef := by
  rw [← exp_tensorLog A hA]
  exact ExponentialDual.exp_posDef (tensorLog_isHermitian A)

/-- The spectral logarithm of a positive-definite tensor is its actual
Kronecker sum of the local logarithms. -/
theorem matrixLog_tensor (A : ι → Matrix Bool Bool ℝ) (hA : ∀ r, (A r).PosDef) :
    EntropyCompletion.matrixLog (tensor A) = tensorLog A := by
  rw [← exp_tensorLog A hA, ExponentialDual.matrixLog_exp (tensorLog_isHermitian A)]

omit [DecidableEq ι] in
/-- Strictly positive local entries give strictly positive tensor entries. -/
theorem tensor_entry_pos (A : ι → Matrix Bool Bool ℝ)
    (hA : ∀ r x y, 0 < A r x y) (z w : ι → Bool) : 0 < tensor A z w :=
  Finset.prod_pos (fun r _ => hA r (z r) (w r))

/-- Every edge of the cube reads off precisely its local logarithmic weight. -/
theorem tensorLog_flip {d : ℕ} (A : Fin d → Matrix Bool Bool ℝ)
    (z : Boolean.Cube d) (r : Fin d) :
    tensorLog A z (Boolean.flip z r) = EntropyCompletion.matrixLog (A r) false true := by
  have ht (s : Fin d) : coordinateLift s (EntropyCompletion.matrixLog (A s)) z
      (Boolean.flip z r) = if s = r then EntropyCompletion.matrixLog (A r) false true else 0 := by
    by_cases hsr : s = r
    · subst s
      rw [if_pos rfl, coordinateLift_apply_of_eq r _ z _ (by
        intro k hk
        simp [Boolean.flip_apply_ne z r k hk])]
      rw [Boolean.flip_apply_same]
      have hh : (EntropyCompletion.matrixLog (A r)).IsHermitian := IsSelfAdjoint.log
      have hs := hh.apply false true
      cases hz : z r
      · rfl
      · simpa only [Bool.not_true, star_trivial] using hs
    · rw [if_neg hsr]
      apply coordinateLift_apply_eq_zero
      intro h
      have he := h r (Ne.symm hsr)
      rw [Boolean.flip_apply_same] at he
      cases hz : z r <;> simp [hz] at he
  simp only [tensorLog, Matrix.sum_apply, ht]
  simp


/-- Away from the diagonal and single-coordinate flips, the logarithmic
Kronecker sum is exactly zero. -/
theorem tensorLog_nonedge {d : ℕ} (A : Fin d → Matrix Bool Bool ℝ)
    (z w : Boolean.Cube d) (hzw : z ≠ w)
    (hn : ∀ r, w ≠ Boolean.flip z r) : tensorLog A z w = 0 := by
  simp only [tensorLog, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro r _
  apply coordinateLift_apply_eq_zero
  intro ho
  have hcoord : z r ≠ w r := by
    intro hr
    apply hzw
    funext k
    by_cases hk : k = r
    · subst k; exact hr
    · exact ho k hk
  have hneg : w r = !(z r) := by
    cases hz : z r <;> cases hw : w r <;> simp_all
  apply hn r
  funext k
  by_cases hk : k = r
  · subst k; simpa only [Boolean.flip_apply_same] using hneg
  · simpa only [Boolean.flip_apply_ne z r k hk] using (ho k hk).symm

/-- The true tensor logarithm has the strictly positive local logarithm as each
coordinate edge weight. -/
theorem matrixLog_tensor_flip_pos {d : ℕ} (A : Fin d → Matrix Bool Bool ℝ)
    (hA : ∀ r, (A r).PosDef) (hv : ∀ r, 0 < A r false true)
    (z : Boolean.Cube d) (r : Fin d) :
    0 < EntropyCompletion.matrixLog (tensor A) z (Boolean.flip z r) := by
  rw [matrixLog_tensor A hA, tensorLog_flip]
  exact matrixLog_offDiagonal_pos (hA r) (hv r)

/-- Every actual cube edge has a strictly positive spectral-logarithm entry. -/
theorem matrixLog_tensor_edge_pos {d : ℕ} (A : Fin d → Matrix Bool Bool ℝ)
    (hA : ∀ r, (A r).PosDef) (hv : ∀ r, 0 < A r false true)
    (z w : Boolean.Cube d) (he : (Boolean.cubeGraph d).Adj z w) :
    0 < EntropyCompletion.matrixLog (tensor A) z w := by
  obtain ⟨r, rfl⟩ := (Boolean.hammingGraph_adj_iff_flip z w).mp he
  exact matrixLog_tensor_flip_pos A hA hv z r

/-- Section 5.1's support assertion: the genuine spectral logarithm of a
positive-definite Boolean tensor has precisely the Cartesian cube support. -/
theorem matrixLog_tensor_support {d : ℕ} (A : Fin d → Matrix Bool Bool ℝ)
    (hA : ∀ r, (A r).PosDef) (hv : ∀ r, 0 < A r false true) :
    LogarithmicSupport.offDiagonalSupport (EntropyCompletion.matrixLog (tensor A))
      (show (EntropyCompletion.matrixLog (tensor A)).IsHermitian from IsSelfAdjoint.log) =
      Boolean.cubeGraph d := by
  ext z w
  rw [LogarithmicSupport.offDiagonalSupport_adj]
  change (_ ∧ _) ↔ (CartesianGeometry.hammingGraph (fun _ : Fin d => Bool)).Adj z w
  rw [Boolean.hammingGraph_adj_iff_flip]
  constructor
  · rintro ⟨hzw, hne⟩
    by_contra hn
    apply hne
    rw [matrixLog_tensor A hA]
    exact tensorLog_nonedge A z w hzw (not_exists.mp hn)
  · rintro ⟨r, rfl⟩
    exact ⟨Ne.symm (Boolean.flip_ne_self z r),
      ne_of_gt (matrixLog_tensor_flip_pos A hA hv z r)⟩

/-- The logarithmic support of a positive-definite Boolean tensor is connected,
including the zero-dimensional one-vertex tensor. -/
theorem matrixLog_tensor_support_connected {d : ℕ} (A : Fin d → Matrix Bool Bool ℝ)
    (hA : ∀ r, (A r).PosDef) (hv : ∀ r, 0 < A r false true) :
    (LogarithmicSupport.offDiagonalSupport (EntropyCompletion.matrixLog (tensor A))
      (show (EntropyCompletion.matrixLog (tensor A)).IsHermitian from IsSelfAdjoint.log)).Connected := by
  rw [matrixLog_tensor_support A hA hv]
  exact Boolean.cubeGraph_connected d


section ScalarNormalization
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Positive scalar normalization contributes only a scalar identity to the
actual spectral logarithm. -/
theorem matrixLog_pos_smul {N : Matrix V V ℝ} (hN : N.PosDef)
    {c : ℝ} (hc : 0 < c) :
    EntropyCompletion.matrixLog (c • N) =
      Real.log c • (1 : Matrix V V ℝ) + EntropyCompletion.matrixLog N := by
  have hscalar : (Real.log c • (1 : Matrix V V ℝ)).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [Matrix.one_apply, eq_comm]
  have hsum := hscalar.add (show (EntropyCompletion.matrixLog N).IsHermitian from IsSelfAdjoint.log)
  have he : NormedSpace.exp ℝ
      (Real.log c • (1 : Matrix V V ℝ) + EntropyCompletion.matrixLog N) = c • N := by
    rw [add_comm, TraceExponential.exp_add_smul_one, KernelContinuation.exp_matrixLog hN,
      Real.exp_log hc]
  rw [← he, ExponentialDual.matrixLog_exp hsum]

/-- Scalar normalization does not change any off-diagonal logarithmic entry. -/
theorem matrixLog_pos_smul_offDiagonal {N : Matrix V V ℝ} (hN : N.PosDef)
    {c : ℝ} (hc : 0 < c) (i j : V) (hij : i ≠ j) :
    EntropyCompletion.matrixLog (c • N) i j = EntropyCompletion.matrixLog N i j := by
  rw [matrixLog_pos_smul hN hc]
  simp [Matrix.one_apply_ne hij]

/-- Scalar normalization leaves the actual logarithmic support unchanged. -/
theorem matrixLog_pos_smul_support {N : Matrix V V ℝ} (hN : N.PosDef)
    {c : ℝ} (hc : 0 < c) :
    LogarithmicSupport.offDiagonalSupport (EntropyCompletion.matrixLog (c • N))
      (show (EntropyCompletion.matrixLog (c • N)).IsHermitian from IsSelfAdjoint.log) =
    LogarithmicSupport.offDiagonalSupport (EntropyCompletion.matrixLog N)
      (show (EntropyCompletion.matrixLog N).IsHermitian from IsSelfAdjoint.log) := by
  ext i j
  simp only [LogarithmicSupport.offDiagonalSupport_adj]
  apply and_congr_right
  intro hij
  rw [matrixLog_pos_smul_offDiagonal hN hc i j hij]
end ScalarNormalization

/-- The scalar-normalized tensor in equation (5.1) has the true cube support. -/
theorem matrixLog_smul_tensor_support {d : ℕ} (A : Fin d → Matrix Bool Bool ℝ)
    (hA : ∀ r, (A r).PosDef) (hv : ∀ r, 0 < A r false true)
    {c : ℝ} (hc : 0 < c) :
    LogarithmicSupport.offDiagonalSupport (EntropyCompletion.matrixLog (c • tensor A))
      (show (EntropyCompletion.matrixLog (c • tensor A)).IsHermitian from IsSelfAdjoint.log) =
      Boolean.cubeGraph d := by
  rw [matrixLog_pos_smul_support (tensor_posDef A hA) hc, matrixLog_tensor_support A hA hv]

/-- Positive scalar normalization preserves the positive logarithmic cube weights. -/
theorem matrixLog_smul_tensor_edge_pos {d : ℕ} (A : Fin d → Matrix Bool Bool ℝ)
    (hA : ∀ r, (A r).PosDef) (hv : ∀ r, 0 < A r false true)
    {c : ℝ} (hc : 0 < c) (z w : Boolean.Cube d) (he : (Boolean.cubeGraph d).Adj z w) :
    0 < EntropyCompletion.matrixLog (c • tensor A) z w := by
  rw [matrixLog_pos_smul_offDiagonal (tensor_posDef A hA) hc z w he.ne]
  exact matrixLog_tensor_edge_pos A hA hv z w he

end PlanarHom.BooleanLogPositivity



