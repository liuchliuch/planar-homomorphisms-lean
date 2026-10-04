import PlanarHom.AlgebraicRealSignInterval
import PlanarHom.IntervalBisectionMachines

/-! # Exact rational-grid approximation of a fixed isolated algebraic root -/

namespace PlanarHom.AlgebraicRealApproximationAlgorithm

def grid (l u : ℚ) (N t : ℕ) : ℚ := l+(u-l)*(t:ℚ)/(N:ℚ)

def test (p : Polynomial ℚ) (l u : ℚ) (N t : ℕ) : Bool := decide (0 ≤ p.eval (grid l u N t))

def index (p : Polynomial ℚ) (l u : ℚ) (N : ℕ) : ℕ :=
  IntervalBisection.cut (test p l u) N N

def approximate (p : Polynomial ℚ) (l u : ℚ) (N : ℕ) : ℚ :=
  grid l u N (index p l u N)

theorem grid_zero (l u : ℚ) (N : ℕ) : grid l u N 0 = l := by simp [grid]

theorem grid_self (l u : ℚ) (N : ℕ) (hN : N ≠ 0) : grid l u N N = u := by
  have h : (N:ℚ) ≠ 0 := by exact_mod_cast hN
  unfold grid
  field_simp
  ring

theorem grid_mono (l u : ℚ) (hlu : l ≤ u) (N s t : ℕ) (hst : s ≤ t) :
    grid l u N s ≤ grid l u N t := by
  unfold grid
  gcongr
  · exact sub_nonneg.mpr hlu

theorem grid_bounds (l u : ℚ) (hlu : l ≤ u) (N : ℕ) (hN : N ≠ 0) (t : ℕ) (ht : t ≤ N) :
    l ≤ grid l u N t ∧ grid l u N t ≤ u := by
  constructor
  · simpa only [grid_zero] using grid_mono l u hlu N 0 t (Nat.zero_le _)
  · simpa only [grid_self l u N hN] using grid_mono l u hlu N t N ht

theorem approximate_error (p : Polynomial ℚ) (l u : ℚ) (a : ℝ)
    (hl : (l:ℝ) < a) (hu : a < (u:ℝ))
    (hs : ∀ t : ℚ, l ≤ t → t ≤ u → (0 ≤ p.eval t ↔ a ≤ (t:ℝ)))
    (N : ℕ) (hN : 0 < N) :
    |(approximate p l u N : ℝ)-a| ≤ ((u-l:ℚ):ℝ)/(N:ℝ) := by
  have hlu : l ≤ u := by exact_mod_cast (le_of_lt (hl.trans hu))
  have htest (t : ℕ) (ht : t ≤ N) : test p l u N t = true ↔ a ≤ (grid l u N t : ℝ) := by
    simp only [test, decide_eq_true_eq]
    exact hs _ (grid_bounds l u hlu N hN.ne' t ht).1 (grid_bounds l u hlu N hN.ne' t ht).2
  have hcut := IntervalBisection.cut_spec (test p l u) N N (by
    intro s t hst ht hs'
    apply (htest t ht).mpr
    have hh := (htest s (hst.trans ht)).mp hs'
    have hm : (grid l u N s : ℝ) ≤ (grid l u N t : ℝ) := by
      exact_mod_cast grid_mono l u hlu N s t hst
    exact hh.trans hm)
  change index p l u N ≤ N+1 ∧
    ∀ t ≤ N, test p l u N t = true ↔ index p l u N ≤ t at hcut
  have hkN : index p l u N ≤ N := by
    apply (hcut.2 N le_rfl).mp
    apply (htest N le_rfl).mpr
    simpa only [grid_self l u N hN.ne'] using hu.le
  have hkpos : 0 < index p l u N := by
    by_contra hk
    have hz : index p l u N = 0 := by omega
    have h0 := (htest 0 (Nat.zero_le _)).mp ((hcut.2 0 (Nat.zero_le _)).mpr (by omega))
    rw [grid_zero] at h0
    linarith
  have hklo : a ≤ (grid l u N (index p l u N) : ℝ) :=
    (htest _ hkN).mp ((hcut.2 _ hkN).mpr le_rfl)
  have hkprev : (grid l u N (index p l u N-1) : ℝ) < a := by
    by_contra hh
    have hh' := (htest _ (show index p l u N-1 ≤ N by omega)).mpr (le_of_not_gt hh)
    have hi := (hcut.2 _ (show index p l u N-1 ≤ N by omega)).mp hh'
    omega
  have hstep : (grid l u N (index p l u N) : ℝ)-
      (grid l u N (index p l u N-1) : ℝ) = ((u-l:ℚ):ℝ)/(N:ℝ) := by
    have hk : ((index p l u N-1:ℕ):ℝ)+1 = (index p l u N:ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hkpos
    simp only [grid, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast]
    rw [← hk]
    ring
  unfold approximate
  rw [abs_of_nonneg (sub_nonneg.mpr hklo)]
  linarith

end PlanarHom.AlgebraicRealApproximationAlgorithm
