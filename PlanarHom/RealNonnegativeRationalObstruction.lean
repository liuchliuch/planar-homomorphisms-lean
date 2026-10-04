import PlanarHom.RealApproximationProductCompatibility
import PlanarHom.FixedChartClosedness
import Mathlib.Analysis.SpecificLimits.Basic

/-! NEW reconstruction: fixed-support closedness and exact rational
approximation give an actual fixed rational obstruction to the same tractable
class. No abstract neighborhood or availability certificate is assumed. -/
noncomputable section
open Classical Filter
open scoped Topology
namespace PlanarHom.FixedRealApproximation
variable {q : ℕ}

theorem rational_obstruction (M : Matrix (Fin q) (Fin q) ℝ)
    (hs : ∀i j, M i j = M j i) (hnn : ∀i j, 0 ≤ M i j)
    (hbad : ¬ Structures.NonnegativeClass M) :
    ∃N : Matrix (Fin q) (Fin q) ℚ,
      (∀i j, N i j = N j i) ∧ (∀i j, 0 ≤ N i j) ∧
      (∀i j, N i j = 0 ↔ M i j = 0) ∧
      ¬Structures.NonnegativeClass (fun i j => (N i j : ℝ)) ∧
      ProductCompatibility.Compatible (fun p : Fin q × Fin q => M p.1 p.2)
        (fun p => (N p.1 p.2 : ℝ)) := by
  have hex (k : ℕ) := RelationApproximation.rational_approximation_with_zeros
    (fun p : Fin q × Fin q => M p.1 p.2) (1 / ((k : ℝ) + 1)) (by positivity)
  choose R hz ha hsg hc using hex
  have hsym (k : ℕ) (i j : Fin q) : R k (i,j) = R k (j,i) := by
    apply Rat.cast_injective (α := ℝ)
    apply RelationApproximation.equal_entries_of_compatible
      (fun p hp => by exact_mod_cast (hz k p).mpr hp) (hc k) (hs i j)
  have hnonneg (k : ℕ) (p : Fin q × Fin q) : 0 ≤ R k p := by
    have hsign := hsg k p
    by_contra h
    have hneg : (R k p : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge h)
    by_cases hm : M p.1 p.2 = 0
    · have hr := (hz k p).mpr hm
      simp [hr] at h
    · have hmpos : 0 < M p.1 p.2 := lt_of_le_of_ne (hnn _ _) (Ne.symm hm)
      rw [Real.sign_of_neg hneg, Real.sign_of_pos hmpos] at hsign
      norm_num at hsign
  have hsupport (k : ℕ) : FixedChartClosedness.HasSupport (fun i j => M i j ≠ 0)
      (fun i j => (R k (i,j) : ℝ)) := by
    constructor
    · intro i j hm
      have hR : R k (i,j) ≠ 0 := fun h => hm ((hz k (i,j)).mp h)
      have hp : 0 < R k (i,j) := lt_of_le_of_ne (hnonneg k (i,j)) (Ne.symm hR)
      change (0 : ℝ) < (R k (i,j) : ℝ)
      exact_mod_cast hp
    · intro i j hm
      simp only [not_not] at hm
      change (R k (i,j) : ℝ) = 0
      exact_mod_cast (hz k (i,j)).mpr hm
  have hMsupport : FixedChartClosedness.HasSupport (fun i j => M i j ≠ 0) M := by
    exact ⟨fun i j h => lt_of_le_of_ne (hnn i j) (Ne.symm h), fun _ _ h => not_not.mp h⟩
  have hlim (i j : Fin q) : Tendsto (fun k => (R k (i,j) : ℝ)) atTop (𝓝 (M i j)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Real.dist_eq] using (ha k (i,j)).le
  have hexBad : ∃k, ¬Structures.NonnegativeClass (fun i j => (R k (i,j) : ℝ)) := by
    by_contra h
    have hall : ∀k, Structures.NonnegativeClass (fun i j => (R k (i,j) : ℝ)) := by simpa using h
    exact hbad (FixedChartClosedness.nonnegativeClass_of_tendsto_fixedSupport
      (fun i j => M i j ≠ 0) _ M hsupport hMsupport hall hlim)
  obtain ⟨k,hk⟩ := hexBad
  exact ⟨fun i j => R k (i,j), hsym k, fun i j => hnonneg k (i,j),
    fun i j => hz k (i,j), hk, hc k⟩

end PlanarHom.FixedRealApproximation
