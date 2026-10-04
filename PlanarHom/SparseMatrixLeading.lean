import PlanarHom.SparseMatrixOrders

/-!
# Leading coefficients along shortest graph paths

The input hypotheses are first-order edge expansions and graph support. The
leading coefficient of a shortest-distance matrix power is proved by induction;
diagonal factors cannot occur at that degree.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients

/-- An expansion with an error of one higher order bounds the function itself. -/
theorem isBigO_of_leading {f : ℝ → ℝ} (a : ℝ) (n : ℕ)
    (h : (fun t => f t - a * t ^ n) =O[𝓝 0] (fun t : ℝ => t ^ (n + 1))) :
    f =O[𝓝 0] (fun t : ℝ => t ^ n) := by
  have he := h.trans (pow_isBigO_pow (Nat.le_succ n))
  have hl := (isBigO_refl (fun t : ℝ => t ^ n) (𝓝 0)).const_mul_left a
  simpa only [sub_add_cancel] using he.add hl

/-- Actual leading coefficients multiply and their orders add. -/
theorem mul_leading_isBigO {f g : ℝ → ℝ} (a b : ℝ) (m n : ℕ)
    (hf : (fun t => f t - a * t ^ m) =O[𝓝 0] (fun t : ℝ => t ^ (m + 1)))
    (hg : (fun t => g t - b * t ^ n) =O[𝓝 0] (fun t : ℝ => t ^ (n + 1))) :
    (fun t => f t * g t - (a * b) * t ^ (m + n)) =O[𝓝 0]
      (fun t : ℝ => t ^ (m + n + 1)) := by
  have h₁ := hf.mul (isBigO_of_leading b n hg)
  have h₂ := ((isBigO_refl (fun t : ℝ => t ^ m) (𝓝 0)).const_mul_left a).mul hg
  have h₁' : (fun t => (f t - a * t ^ m) * g t) =O[𝓝 0]
      (fun t : ℝ => t ^ (m + n + 1)) := by
    convert h₁ using 1
    ext t
    rw [← pow_add]
    congr 1
    omega
  have h₂' : (fun t => a * t ^ m * (g t - b * t ^ n)) =O[𝓝 0]
      (fun t : ℝ => t ^ (m + n + 1)) := by
    simpa only [← pow_add, Nat.add_assoc] using h₂
  convert h₁'.add h₂' using 1
  ext t
  rw [pow_add]
  ring

/-- A leading expansion may be raised to any natural power. -/
theorem pow_leading_isBigO {f : ℝ → ℝ} (a : ℝ) (n s : ℕ)
    (hf : (fun t => f t - a * t ^ n) =O[𝓝 0] (fun t : ℝ => t ^ (n + 1))) :
    (fun t => f t ^ s - a ^ s * t ^ (n * s)) =O[𝓝 0]
      (fun t : ℝ => t ^ (n * s + 1)) := by
  induction s with
  | zero => simpa using (isBigO_zero (E' := ℝ) (fun t : ℝ => t) (𝓝 0))
  | succ s ih =>
    have h := mul_leading_isBigO (a ^ s) a (n * s) n ih hf
    simpa only [pow_succ, Nat.mul_succ] using h

/-- The coefficient in an expansion with a one-order-higher error is unique. -/
theorem leading_coefficient_unique {f : ℝ → ℝ} (a b : ℝ) (n : ℕ)
    (ha : (fun t => f t - a * t ^ n) =O[𝓝 0] (fun t : ℝ => t ^ (n + 1)))
    (hb : (fun t => f t - b * t ^ n) =O[𝓝 0] (fun t : ℝ => t ^ (n + 1))) : a = b := by
  by_contra hab
  have hd : (fun t : ℝ => (a - b) * t ^ n) =O[𝓝 0] (fun t : ℝ => t ^ (n + 1)) := by
    convert hb.sub ha using 1
    ext t
    ring
  have hl := hd.trans_isLittleO (isLittleO_pow_pow (Nat.lt_succ_self n))
  have hself := (isLittleO_const_mul_left_iff (sub_ne_zero.mpr hab)).mp hl
  have hbound := hself.def (by norm_num : (0 : ℝ) < 1 / 2)
  have hbound' := hbound.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hp : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, htpos⟩ := (hbound'.and hp).exists
  have hpos : 0 < ‖t ^ n‖ := norm_pos_iff.mpr (pow_ne_zero _ (ne_of_gt htpos))
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At shortest distance, only off-diagonal edge leading terms contribute. -/
theorem supported_pow_distance_leading_isBigO (G : SimpleGraph V) (hG : G.Connected)
    (A : ℝ → Matrix V V ℝ) (B : Matrix V V ℝ) (s : ℕ)
    (hA : ∀ᶠ t in 𝓝 0, SupportedOn G (A t)) (hB : SupportedOn G B)
    (hleading : ∀ i j, G.Adj i j →
      (fun t => A t i j - B i j * t ^ s) =O[𝓝 0] (fun t : ℝ => t ^ (s + 1)))
    (n : ℕ) (i j : V) (hd : G.dist i j = n) :
    (fun t => (A t ^ n) i j - (B ^ n) i j * t ^ (s * n)) =O[𝓝 0]
      (fun t : ℝ => t ^ (s * n + 1)) := by
  induction n generalizing i j with
  | zero =>
    simpa only [pow_zero, Nat.mul_zero, mul_one, sub_self, Nat.zero_add, pow_one] using
      (isBigO_zero (E' := ℝ) (fun t : ℝ => t) (𝓝 0))
  | succ n ih =>
    have hterm : ∀ k : V,
        (fun t => A t i k * (A t ^ n) k j -
          (B i k * (B ^ n) k j) * t ^ (s * (n + 1))) =O[𝓝 0]
            (fun t : ℝ => t ^ (s * (n + 1) + 1)) := by
      intro k
      by_cases hik : i = k
      · subst k
        have hn : n < G.dist i j := by omega
        have hb := supported_pow_entry_zero G hG B hB n i j hn
        apply isBigO_of_eventually_zero
        filter_upwards [eventually_supported_pow_entry_zero G hG A hA n i j hn] with t ht
        rw [ht, hb]
        ring
      · by_cases hadj : G.Adj i k
        · have htri := hG.dist_triangle (u := i) (v := k) (w := j)
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj, hd] at htri
          by_cases hkn : G.dist k j = n
          · have h := mul_leading_isBigO (B i k) ((B ^ n) k j) s (s * n)
              (hleading i k hadj) (ih k j hkn)
            simpa only [Nat.mul_succ, Nat.add_comm s (s * n)] using h
          · have hn : n < G.dist k j := by omega
            have hb := supported_pow_entry_zero G hG B hB n k j hn
            apply isBigO_of_eventually_zero
            filter_upwards [eventually_supported_pow_entry_zero G hG A hA n k j hn] with t ht
            rw [ht, hb]
            ring
        · have hb := hB i k hik hadj
          apply isBigO_of_eventually_zero
          filter_upwards [hA] with t ht
          rw [ht i k hik hadj, hb]
          ring
    have hsum := IsBigO.sum (s := Finset.univ) (fun k _ => hterm k)
    convert hsum using 1
    ext t
    simp only [pow_succ', Matrix.mul_apply, Finset.sum_sub_distrib, Finset.sum_mul]

end PlanarHom.MatrixLogCoefficients
