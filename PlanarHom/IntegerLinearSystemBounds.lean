import PlanarHom.IntegerCoordinateBounds
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Cramer's rule with explicit integer numerator and denominator bounds. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace PlanarHom.IntegerLinearSystemBounds
open IntegerCoordinateBounds

variable {n : ℕ}

/-- The elementary Leibniz bound, with the dimension fixed in applications. -/
theorem det_natAbs_le (H : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hH : ∀ i j, (H i j).natAbs ≤ B) : H.det.natAbs ≤ n.factorial * B ^ n := by
  rw [Matrix.det_apply']
  apply (natAbs_sum_le _ _).trans
  have hp (σ : Equiv.Perm (Fin n)) :
      (((Equiv.Perm.sign σ : ℤ) * ∏ i, H (σ i) i)).natAbs ≤ B ^ n := by
    rw [Int.natAbs_mul, Int.units_natAbs, one_mul]
    change Int.natAbsHom (∏ i, H (σ i) i) ≤ _
    rw [map_prod]
    simpa using Finset.prod_le_prod' (s := Finset.univ) (fun i _ => hH (σ i) i)
  simpa [Fintype.card_perm] using Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hp σ)

/-- The numerator produced by a Cramer column replacement obeys the same bound. -/
theorem cramer_natAbs_le (H : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (B : ℕ)
    (hH : ∀ i j, (H i j).natAbs ≤ B) (hb : ∀ i, (b i).natAbs ≤ B) (i : Fin n) :
    (Matrix.cramer H b i).natAbs ≤ n.factorial * B ^ n := by
  rw [Matrix.cramer_apply]
  apply det_natAbs_le
  intro j k
  rw [Matrix.updateCol_apply]
  split <;> simp_all

/-- Convert a fraction with a signed nonzero denominator to `mkRat` without height growth. -/
theorem div_eq_mkRat_sign (z d : ℤ) (hd : d ≠ 0) :
    (z : ℚ) / (d : ℚ) = mkRat (z * d.sign) d.natAbs := by
  have hsign : (d.sign : ℚ) * (d : ℚ) = (d.natAbs : ℚ) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) (Int.sign_mul_self d)
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hn : (d.natAbs : ℚ) ≠ 0 := by exact_mod_cast (Int.natAbs_ne_zero.mpr hd)
  rw [Rat.mkRat_eq_div, Int.cast_mul]
  apply (div_eq_div_iff hdq hn).mpr
  rw [← hsign]
  ring

/-- Exact Cramer fraction for a solution over the rationals. -/
theorem solution_eq_cramer (H : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ)
    (x : Fin n → ℚ) (hdet : H.det ≠ 0)
    (hx : (fun i j => (H i j : ℚ)) *ᵥ x = fun i => (b i : ℚ)) (i : Fin n) :
    x i = (Matrix.cramer H b i : ℚ) / (H.det : ℚ) := by
  let Hq : Matrix (Fin n) (Fin n) ℚ := fun i j => H i j
  let bq : Fin n → ℚ := fun i => b i
  have hd : Hq.det = (H.det : ℚ) := (RingHom.map_det (Int.castRingHom ℚ) H).symm
  have hc : (Matrix.cramer Hq bq i) = (Matrix.cramer H b i : ℚ) := by
    rw [Matrix.cramer_apply, Matrix.cramer_apply]
    have hm : Hq.updateCol i bq = (Int.castRingHom ℚ).mapMatrix (H.updateCol i b) := by
      ext j k
      simp only [Matrix.updateCol_apply, Hq, bq, RingHom.mapMatrix_apply, Matrix.map_apply]
      split <;> rfl
    rw [hm]
    exact (RingHom.map_det (Int.castRingHom ℚ) (H.updateCol i b)).symm
  change Hq *ᵥ x = bq at hx
  have heq : Hq.det • x = Matrix.cramer Hq bq := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hx, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  apply (eq_div_iff (by exact_mod_cast hdet)).mpr
  simpa only [Pi.smul_apply, smul_eq_mul, hd, hc, mul_comm] using congrFun heq i

/-- Every solution of a nonsingular integer linear system has bounded rational representatives. -/
theorem solution_representatives (H : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ)
    (x : Fin n → ℚ) (hdet : H.det ≠ 0)
    (hx : (fun i j => (H i j : ℚ)) *ᵥ x = fun i => (b i : ℚ)) (B : ℕ)
    (hH : ∀ i j, (H i j).natAbs ≤ B) (hb : ∀ i, (b i).natAbs ≤ B) (i : Fin n) :
    ∃ z : ℤ, ∃ d : ℕ, 0 < d ∧ x i = mkRat z d ∧
      z.natAbs ≤ n.factorial * B ^ n ∧ d ≤ n.factorial * B ^ n := by
  have hxi := solution_eq_cramer H b x hdet hx i
  refine ⟨Matrix.cramer H b i * H.det.sign, H.det.natAbs,
    Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hdet), ?_, ?_, det_natAbs_le H B hH⟩
  · exact hxi.trans (div_eq_mkRat_sign _ _ hdet)
  · rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hdet, mul_one]
    exact cramer_natAbs_le H b B hH hb i

end PlanarHom.IntegerLinearSystemBounds
