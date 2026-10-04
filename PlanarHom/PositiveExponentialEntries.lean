import PlanarHom.SparseMatrixOrders
import PlanarHom.PositivePowers
import PlanarHom.TraceExponential

/-!
# Strict positivity of exponentials with positive connected edge support

This proves condition (iii) in the source Lemma 4.2. Diagonal entries may have
any sign: a scalar identity shift makes the matrix nonnegative, every pair has
a positive walk contribution in the actual exponential series, and the scalar
exponential shift is strictly positive.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonnegative matrix with a positive graph walk has a strictly positive
corresponding entry in its genuine exponential. -/
theorem exp_entry_pos_of_nonneg_walk (A : Matrix V V ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (G : SimpleGraph V) (hedge : ∀ i j, G.Adj i j → 0 < A i j)
    {i j : V} (p : G.Walk i j) : 0 < NormedSpace.exp ℝ A i j := by
  have hsum : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * (A ^ n) i j)
      (NormedSpace.exp ℝ A i j) := by
    simpa only [entryCLM_apply, map_smul, smul_eq_mul] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).mapL (entryCLM i j)
  have hnonneg : ∀ n : ℕ, 0 ≤ (n.factorial : ℝ)⁻¹ * (A ^ n) i j := by
    intro n
    exact mul_nonneg (by positivity) (PositivePowers.power_nonneg A hA n i j)
  have hpos : 0 < (p.length.factorial : ℝ)⁻¹ * (A ^ p.length) i j := by
    apply mul_pos
    · positivity
    · exact PositivePowers.power_pos_of_walk A hA G (fun {a b} hab => hedge a b hab) p
  rw [← hsum.tsum_eq]
  exact hsum.summable.tsum_pos hnonneg p.length hpos

/-- A finite real matrix can always be shifted to make its diagonal nonnegative. -/
theorem exists_nonneg_diagonal_shift (A : Matrix V V ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, 0 ≤ A i i + c := by
  let c : ℝ := ∑ i, |A i i|
  refine ⟨c, Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  intro i
  have hle : |A i i| ≤ c := Finset.single_le_sum (f := fun j => |A j j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  linarith [neg_abs_le (A i i)]

/-- Connected positive off-diagonal support forces entrywise exponential
positivity, even when the original diagonal is arbitrarily signed. -/
theorem exp_entry_pos_of_positive_connected_support (A : Matrix V V ℝ)
    (G : SimpleGraph V) (hG : G.Connected) (hsupport : SupportedOn G A)
    (hedge : ∀ i j, G.Adj i j → 0 < A i j) (i j : V) :
    0 < NormedSpace.exp ℝ A i j := by
  obtain ⟨c, hc, hdiag⟩ := exists_nonneg_diagonal_shift A
  let B : Matrix V V ℝ := A + c • 1
  have hB : ∀ a b, 0 ≤ B a b := by
    intro a b
    by_cases hab : a = b
    · subst b
      simpa only [B, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one] using hdiag a
    · by_cases hadj : G.Adj a b
      · simpa only [B, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hab,
          smul_eq_mul, mul_zero, add_zero] using (hedge a b hadj).le
      · simp only [B, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hab,
          smul_eq_mul, mul_zero, add_zero, hsupport a b hab hadj, le_refl]
  have hedgeB : ∀ a b, G.Adj a b → 0 < B a b := by
    intro a b hab
    simpa only [B, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hab.ne,
      smul_eq_mul, mul_zero, add_zero] using hedge a b hab
  obtain ⟨p, hp⟩ := hG.exists_isPath i j
  have hpos := exp_entry_pos_of_nonneg_walk B hB G hedgeB p
  have hshift := TraceExponential.exp_add_smul_one A c
  have hentry := congrArg (fun M : Matrix V V ℝ => M i j) hshift
  change NormedSpace.exp ℝ B i j = Real.exp c * NormedSpace.exp ℝ A i j at hentry
  rw [hentry] at hpos
  exact (mul_pos_iff_of_pos_left (Real.exp_pos c)).mp hpos

/-- Every positive-time exponential entry of a Hermitian logarithm with
positive connected edge support is strictly positive. -/
theorem exp_positive_time_entry_pos (L : Matrix V V ℝ) (hL : L.IsHermitian)
    (hG : (LogarithmicSupport.offDiagonalSupport L hL).Connected)
    (hedge : ∀ i j, (LogarithmicSupport.offDiagonalSupport L hL).Adj i j → 0 < L i j)
    (t : ℝ) (ht : 0 < t) (i j : V) :
    0 < NormedSpace.exp ℝ (t • L) i j := by
  apply exp_entry_pos_of_positive_connected_support (t • L)
    (LogarithmicSupport.offDiagonalSupport L hL) hG
  · intro a b hab hn
    have hz : L a b = 0 := by
      by_contra hne
      exact hn ⟨hab, hne⟩
    simp [hz]
  · intro a b hab
    exact mul_pos ht (hedge a b hab)

end PlanarHom.MatrixLogCoefficients
