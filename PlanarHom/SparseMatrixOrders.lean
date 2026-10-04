import PlanarHom.MatrixExponentialDistance

/-!
# Graph-distance orders of sparse matrix powers

An off-diagonal step of a sparse matrix curve costs order `s`, while a diagonal
step costs order one. Graph distance therefore gives the exact lower order
`s*d(i,j) + n-d(i,j)` for an entry of its `n`th ordinary matrix power.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A matrix is supported on the diagonal and edges of `G`. -/
def SupportedOn (G : SimpleGraph V) (A : Matrix V V ℝ) : Prop :=
  ∀ i j, i ≠ j → ¬G.Adj i j → A i j = 0

/-- Fewer factors than graph distance cannot contribute, regardless of diagonal signs. -/
theorem supported_pow_entry_zero (G : SimpleGraph V) (hG : G.Connected)
    (A : Matrix V V ℝ) (hA : SupportedOn G A) (n : ℕ) (i j : V)
    (hn : n < G.dist i j) : (A ^ n) i j = 0 := by
  induction n generalizing i j with
  | zero =>
    have hij : i ≠ j := by
      rintro rfl
      rw [G.dist_self] at hn
      omega
    simp [hij]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hik : i = k
    · subst k
      rw [ih i j (by omega), mul_zero]
    · by_cases hadj : G.Adj i k
      · have hd := hG.dist_triangle (u := i) (v := k) (w := j)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at hd
        rw [ih k j (by omega), mul_zero]
      · rw [hA i k hik hadj, zero_mul]

/-- Pointwise sparse power vanishing also holds eventually along a curve. -/
theorem eventually_supported_pow_entry_zero (G : SimpleGraph V) (hG : G.Connected)
    (A : ℝ → Matrix V V ℝ) (hA : ∀ᶠ t in 𝓝 0, SupportedOn G (A t))
    (n : ℕ) (i j : V) (hn : n < G.dist i j) :
    ∀ᶠ t in 𝓝 0, (A t ^ n) i j = 0 :=
  hA.mono fun _ ht => supported_pow_entry_zero G hG _ ht n i j hn

/-- A curve which is eventually zero has any requested asymptotic order. -/
theorem isBigO_of_eventually_zero {α : Type*} {l : Filter α} {f : α → ℝ}
    (hf : ∀ᶠ t in l, f t = 0) (g : α → ℝ) : f =O[l] g := by
  apply IsBigO.of_bound 0
  filter_upwards [hf] with t ht
  simp [ht]

/-- Graph sparsity retains the stronger cost of every required off-diagonal factor. -/
theorem supported_pow_entry_isBigO (G : SimpleGraph V) (hG : G.Connected)
    (A : ℝ → Matrix V V ℝ) (s : ℕ) (hs : 1 ≤ s)
    (hsupport : ∀ᶠ t in 𝓝 0, SupportedOn G (A t))
    (hdiag : ∀ i, (fun t => A t i i) =O[𝓝 0] (fun t : ℝ => t))
    (hedge : ∀ i j, G.Adj i j → (fun t => A t i j) =O[𝓝 0] (fun t : ℝ => t ^ s))
    (n : ℕ) (i j : V) :
    (fun t => (A t ^ n) i j) =O[𝓝 0]
      (fun t : ℝ => t ^ (s * G.dist i j + (n - G.dist i j))) := by
  induction n generalizing i j with
  | zero =>
    by_cases hij : i = j
    · subst j
      simpa only [pow_zero, Matrix.one_apply_eq, G.dist_self, Nat.mul_zero,
        Nat.sub_self, Nat.add_zero] using (isBigO_refl (fun _t : ℝ => (1 : ℝ)) (𝓝 0))
    · have hd := hG.pos_dist_of_ne hij
      exact isBigO_of_eventually_zero
        (eventually_supported_pow_entry_zero G hG A hsupport 0 i j hd) _
  | succ n ih =>
    by_cases hn : n + 1 < G.dist i j
    · exact isBigO_of_eventually_zero
        (eventually_supported_pow_entry_zero G hG A hsupport (n + 1) i j hn) _
    have hdij : G.dist i j ≤ n + 1 := Nat.le_of_not_gt hn
    have hterm : ∀ k : V,
        (fun t => A t i k * (A t ^ n) k j) =O[𝓝 0]
          (fun t : ℝ => t ^ (s * G.dist i j + (n + 1 - G.dist i j))) := by
      intro k
      by_cases hkn : n < G.dist k j
      · apply isBigO_of_eventually_zero
        filter_upwards [eventually_supported_pow_entry_zero G hG A hsupport n k j hkn]
          with t ht
        rw [ht, mul_zero]
      have hdkj : G.dist k j ≤ n := Nat.le_of_not_gt hkn
      by_cases hik : i = k
      · subst k
        have hh := (hdiag i).mul (ih i j)
        convert hh using 1
        ext t
        rw [← pow_succ']
        congr 1
        omega
      · by_cases hadj : G.Adj i k
        · have hh := (hedge i k hadj).mul (ih k j)
          have hd := hG.dist_triangle (u := i) (v := k) (w := j)
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at hd
          have hexp : s * G.dist i j + (n + 1 - G.dist i j) ≤
              s + (s * G.dist k j + (n - G.dist k j)) := by
            have hsub₁ : n + 1 - G.dist i j + G.dist i j = n + 1 := Nat.sub_add_cancel hdij
            have hsub₂ : n - G.dist k j + G.dist k j = n := Nat.sub_add_cancel hdkj
            have hmul : G.dist i j - 1 ≤ G.dist k j := by omega
            have hprod : (s - 1) * G.dist i j ≤ (s - 1) * (G.dist k j + 1) := by
              exact Nat.mul_le_mul_left _ (by omega)
            nlinarith
          have hh' : (fun t => A t i k * (A t ^ n) k j) =O[𝓝 0]
              (fun t : ℝ => t ^ (s + (s * G.dist k j + (n - G.dist k j)))) := by
            simpa only [pow_add] using hh
          exact hh'.trans (pow_isBigO_pow hexp)
        · apply isBigO_of_eventually_zero
          filter_upwards [hsupport] with t ht
          rw [ht i k hik hadj, zero_mul]
    have hsum := IsBigO.sum (s := Finset.univ) (fun k _ => hterm k)
    simpa only [pow_succ', Matrix.mul_apply] using hsum

end PlanarHom.MatrixLogCoefficients
