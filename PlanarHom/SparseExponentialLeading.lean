import PlanarHom.SparseMatrixLeading

/-!
# Shortest-distance leading coefficient of a sparse matrix exponential curve

Off-diagonal factors have order `s` and diagonal factors have order one. The
proof controls every Taylor summand and the true exponential-series remainder.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Taylor polynomial of the matrix exponential at zero. -/
def expMatrixTaylor (A : Matrix V V ℝ) (n : ℕ) : Matrix V V ℝ :=
  ∑ k ∈ Finset.range n, (k.factorial : ℝ)⁻¹ • A ^ k

/-- The genuine exponential Taylor remainder along a first-order matrix curve. -/
theorem exp_sub_expMatrixTaylor_isBigO (A : ℝ → Matrix V V ℝ)
    (hA : A =O[𝓝 0] (fun t : ℝ => t)) (n : ℕ) :
    (fun t => NormedSpace.exp ℝ (A t) - expMatrixTaylor (A t) n) =O[𝓝 0]
      (fun t : ℝ => t ^ n) := by
  have hz : Tendsto A (𝓝 0) (𝓝 0) := hA.trans_tendsto tendsto_id
  have h := (NormedSpace.exp_hasFPowerSeriesAt_zero (𝕂 := ℝ)
    (𝔸 := Matrix V V ℝ)).isBigO_sub_partialSum_pow n
  have hr := (h.comp_tendsto hz).trans (hA.norm_left.pow n)
  simpa only [Function.comp_apply, zero_add, expMatrixTaylor,
    FormalMultilinearSeries.partialSum, NormedSpace.expSeries_apply_eq] using hr

/-- Sparse edge orders at least one and first-order diagonals control the whole matrix. -/
theorem supported_curve_isBigO (G : SimpleGraph V) (A : ℝ → Matrix V V ℝ)
    (s : ℕ) (hs : 1 ≤ s) (hsupport : ∀ᶠ t in 𝓝 0, SupportedOn G (A t))
    (hdiag : ∀ i, (fun t => A t i i) =O[𝓝 0] (fun t : ℝ => t))
    (hedge : ∀ i j, G.Adj i j → (fun t => A t i j) =O[𝓝 0] (fun t : ℝ => t ^ s)) :
    A =O[𝓝 0] (fun t : ℝ => t) := by
  apply matrix_isBigO_of_entries
  intro i j
  by_cases hij : i = j
  · subst j; exact hdiag i
  by_cases hadj : G.Adj i j
  · simpa only [pow_one] using (hedge i j hadj).trans (pow_isBigO_pow hs)
  · apply isBigO_of_eventually_zero
    exact hsupport.mono fun _ ht => ht i j hij hadj

/-- Actual leading term of `exp(A(t))` at graph distance `d`, allowing arbitrary
first-order diagonal terms and using only input edge leading coefficients. -/
theorem supported_exp_distance_leading_isBigO (G : SimpleGraph V) (hG : G.Connected)
    (A : ℝ → Matrix V V ℝ) (B : Matrix V V ℝ) (s : ℕ) (hs : 1 ≤ s)
    (hsupport : ∀ᶠ t in 𝓝 0, SupportedOn G (A t)) (hB : SupportedOn G B)
    (hdiag : ∀ i, (fun t => A t i i) =O[𝓝 0] (fun t : ℝ => t))
    (hleading : ∀ i j, G.Adj i j →
      (fun t => A t i j - B i j * t ^ s) =O[𝓝 0] (fun t : ℝ => t ^ (s + 1)))
    (i j : V) :
    let d := G.dist i j
    (fun t => NormedSpace.exp ℝ (A t) i j -
      ((B ^ d) i j / (d.factorial : ℝ)) * t ^ (s * d)) =O[𝓝 0]
      (fun t : ℝ => t ^ (s * d + 1)) := by
  let d := G.dist i j
  let N := s * d + 1
  have hdN : d < N := by dsimp [N]; nlinarith
  have hedge : ∀ a b, G.Adj a b → (fun t => A t a b) =O[𝓝 0] (fun t : ℝ => t ^ s) :=
    fun a b hab => isBigO_of_leading (B a b) s (hleading a b hab)
  have hA := supported_curve_isBigO G A s hs hsupport hdiag hedge
  have hterm : ∀ k ∈ Finset.range N,
      (fun t => (k.factorial : ℝ)⁻¹ * (A t ^ k) i j -
        if k = d then ((B ^ d) i j / (d.factorial : ℝ)) * t ^ (s * d) else 0)
        =O[𝓝 0] (fun t : ℝ => t ^ N) := by
    intro k hk
    by_cases hkd : k = d
    · subst k
      have h := (supported_pow_distance_leading_isBigO G hG A B s hsupport hB
        hleading d i j rfl).const_mul_left ((d.factorial : ℝ)⁻¹)
      convert h using 1
      ext t
      simp only [ite_true]
      ring
    · simp only [hkd, ite_false, sub_zero]
      by_cases hklt : k < d
      · apply isBigO_of_eventually_zero
        filter_upwards [eventually_supported_pow_entry_zero G hG A hsupport k i j hklt]
          with t ht
        rw [ht, mul_zero]
      · have hp := supported_pow_entry_isBigO G hG A s hs hsupport hdiag hedge k i j
        have hexp : N ≤ s * G.dist i j + (k - G.dist i j) := by
          dsimp [N, d] at *
          omega
        exact (hp.trans (pow_isBigO_pow hexp)).const_mul_left _
  have hsum := IsBigO.sum hterm
  have hsum' : (fun t => expMatrixTaylor (A t) N i j -
      ((B ^ d) i j / (d.factorial : ℝ)) * t ^ (s * d)) =O[𝓝 0]
      (fun t : ℝ => t ^ N) := by
    convert hsum using 1
    ext t
    simp only [expMatrixTaylor, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib]
    simp [hdN]
  have hrem := entry_isBigO (exp_sub_expMatrixTaylor_isBigO A hA N) i j
  have h := hrem.add hsum'
  simpa only [Matrix.sub_apply, sub_add_sub_cancel] using h

end PlanarHom.MatrixLogCoefficients
