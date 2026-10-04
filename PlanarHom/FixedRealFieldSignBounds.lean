import PlanarHom.FixedFieldArithmeticMachines
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean

/-! Quantitative sign separation in a fixed rational basis of a real field. -/
noncomputable section
namespace PlanarHom.FixedRealFieldSign
open scoped BigOperators
variable {K : Type} [Field K] [Algebra ℚ K]
variable {d : ℕ} (basis : Module.Basis (Fin d) ℚ K) (embedding : K →+* ℝ)

def coordinateMass (x : K) : ℕ := ∑ i, (basis.equivFun x i).num.natAbs

def inverseBound (M : ℕ) (x : K) : ℕ := 1 + M * coordinateMass basis x⁻¹

def precision (M : ℕ) (x : K) : ℕ := 4 * inverseBound basis M x * (1 + coordinateMass basis x)

theorem exists_basis_bound : ∃ M : ℕ, 0 < M ∧ ∀ i, |embedding (basis i)| ≤ M := by
  choose f hf using fun i : Fin d => exists_nat_gt |embedding (basis i)|
  refine ⟨1 + ∑ i, f i, by omega, ?_⟩
  intro i
  have hi : f i ≤ ∑ j, f j := Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ i)
  have hi' : (f i : ℝ) ≤ ((∑ j, f j : ℕ) : ℝ) := by exact_mod_cast hi
  push_cast at hi' ⊢
  linarith [hf i]

theorem abs_ratCast_le_num (q : ℚ) : |(q : ℝ)| ≤ (q.num.natAbs : ℝ) := by
  rw [Rat.cast_def, abs_div, ← Int.cast_abs, Int.abs_eq_natAbs]
  simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg q.den : (0 : ℝ) ≤ q.den)]
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  exact div_le_self (Nat.cast_nonneg _) hden

theorem embedding_eq_sum (x : K) :
    embedding x = ∑ i, (basis.equivFun x i : ℝ) * embedding (basis i) := by
  conv_lhs => rw [← basis.sum_equivFun x]
  simp only [map_sum, Algebra.smul_def, map_mul, RingHom.map_rat_algebraMap]
  rfl

theorem abs_embedding_le (M : ℕ) (hM : ∀ i, |embedding (basis i)| ≤ M) (x : K) :
    |embedding x| ≤ M * (coordinateMass basis x : ℝ) := by
  rw [embedding_eq_sum basis embedding x]
  calc
    |∑ i, (basis.equivFun x i : ℝ) * embedding (basis i)| ≤
        ∑ i, |(basis.equivFun x i : ℝ) * embedding (basis i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((basis.equivFun x i).num.natAbs : ℝ) * M := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (abs_ratCast_le_num _) (hM i) (abs_nonneg _) (Nat.cast_nonneg _)
    _ = M * (coordinateMass basis x : ℝ) := by
      simp only [coordinateMass, Nat.cast_sum]
      rw [← Finset.sum_mul, mul_comm]

theorem inverseBound_pos (M : ℕ) (x : K) : 0 < inverseBound basis M x := by
  unfold inverseBound
  omega

theorem abs_embedding_inverse_le (M : ℕ) (hM : ∀ i, |embedding (basis i)| ≤ M) (x : K) :
    |embedding x⁻¹| < (inverseBound basis M x : ℝ) := by
  have hb := abs_embedding_le basis embedding M hM x⁻¹
  simp only [inverseBound, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  linarith

theorem inverseBound_separation (M : ℕ) (hM : ∀ i, |embedding (basis i)| ≤ M)
    (x : K) (hx : x ≠ 0) : 1 / (inverseBound basis M x : ℝ) < |embedding x| := by
  have he : embedding x ≠ 0 := (map_ne_zero embedding).mpr hx
  have ha : 0 < |embedding x| := abs_pos.mpr he
  have hH : (0 : ℝ) < inverseBound basis M x := by exact_mod_cast inverseBound_pos basis M x
  have hb := abs_embedding_inverse_le basis embedding M hM x
  rw [map_inv₀, abs_inv] at hb
  exact (div_lt_iff₀ hH).mpr (by nlinarith [inv_mul_cancel₀ (ne_of_gt ha)])

def approximation (f : Fin d → ℕ → ℚ) (M : ℕ) (x : K) : ℚ :=
  ∑ i, basis.equivFun x i * f i (precision basis M x)

theorem approximation_error (f : Fin d → ℕ → ℚ)
    (hf : ∀ i N, |(f i N : ℝ) - embedding (basis i)| ≤ 1 / ((N : ℝ) + 1))
    (M : ℕ) (x : K) :
    |(approximation basis f M x : ℝ) - embedding x| < 1 / (inverseBound basis M x : ℝ) := by
  let H : ℝ := inverseBound basis M x
  let C : ℝ := coordinateMass basis x
  have hH : 0 < H := by dsimp [H]; exact_mod_cast inverseBound_pos basis M x
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hp : (precision basis M x : ℝ) = 4 * H * (1+C) := by
    simp [precision, H, C]
  have hden : 0 < (precision basis M x : ℝ) + 1 := by positivity
  have herror : |(approximation basis f M x : ℝ) - embedding x| ≤
      C / ((precision basis M x : ℝ) + 1) := by
    rw [approximation, Rat.cast_sum, embedding_eq_sum basis embedding x, ← Finset.sum_sub_distrib]
    simp_rw [Rat.cast_mul, ← mul_sub]
    calc
      |∑ i, (basis.equivFun x i : ℝ) * ((f i (precision basis M x) : ℝ) - embedding (basis i))| ≤
          ∑ i, |(basis.equivFun x i : ℝ) * ((f i (precision basis M x) : ℝ) - embedding (basis i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ((basis.equivFun x i).num.natAbs : ℝ) * (1 / ((precision basis M x : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (abs_ratCast_le_num _) (hf i _) (abs_nonneg _) (Nat.cast_nonneg _)
      _ = C / ((precision basis M x : ℝ) + 1) := by
        simp [C, coordinateMass, Finset.sum_mul, div_eq_mul_inv]
  apply herror.trans_lt
  apply (div_lt_div_iff₀ hden hH).mpr
  rw [hp]
  nlinarith

theorem approximation_positive_iff (f : Fin d → ℕ → ℚ)
    (hf : ∀ i N, |(f i N : ℝ) - embedding (basis i)| ≤ 1 / ((N : ℝ) + 1))
    (M : ℕ) (hM : ∀ i, |embedding (basis i)| ≤ M) (x : K) :
    0 < approximation basis f M x ↔ 0 < embedding x := by
  by_cases hx : x = 0
  · subst x
    simp [approximation]
  have herr := approximation_error basis embedding f hf M x
  have hsep := inverseBound_separation basis embedding M hM x hx
  have herror : |(approximation basis f M x : ℝ) - embedding x| < |embedding x| := herr.trans hsep
  have hs := abs_lt.mp herror
  have he : embedding x ≠ 0 := (map_ne_zero embedding).mpr hx
  have hc : (0 : ℝ) < (approximation basis f M x : ℝ) ↔ 0 < embedding x := by
    rcases lt_or_gt_of_ne he with hn | hp
    · rw [abs_of_neg hn] at hs
      constructor <;> intro h <;> linarith
    · rw [abs_of_pos hp] at hs
      constructor <;> intro h <;> linarith
  exact_mod_cast hc

end PlanarHom.FixedRealFieldSign
