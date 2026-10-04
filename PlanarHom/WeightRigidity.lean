import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Rigidity of positive vertex weights

The finite real inequalities underlying Lemmas 8.3 and 9.3 (and their appendix
versions) of Liu--Meng. Strict positivity and equal row sums separate the extreme
weighted diagonal entries. Equal row and column sums also make a positive
bipartite scaling with constant marginals trivial. The latter statement does not
require symmetry. No computational-complexity conclusion is asserted here.
-/

open scoped BigOperators

namespace PlanarHom.WeightRigidity

variable {I : Type*} [Fintype I]

/-- A strictly positive weighted average is strictly below an upper bound if
at least one coordinate is below it. -/
theorem sum_mul_lt_of_lt (q w : I → ℝ) (M r : ℝ)
    (hq : ∀ i, 0 < q i) (hsum : ∑ i, q i = r)
    (hle : ∀ i, w i ≤ M) (hlt : ∃ i, w i < M) :
    (∑ i, q i * w i) < r * M := by
  classical
  rw [← hsum, Finset.sum_mul]
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_left (hle i) (le_of_lt (hq i))
  · obtain ⟨i, hi⟩ := hlt
    exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hq i)⟩

/-- The analogous strict lower bound for a positive weighted average. -/
theorem lt_sum_mul_of_lt (q w : I → ℝ) (m r : ℝ)
    (hq : ∀ i, 0 < q i) (hsum : ∑ i, q i = r)
    (hle : ∀ i, m ≤ w i) (hlt : ∃ i, m < w i) :
    r * m < ∑ i, q i * w i := by
  classical
  rw [← hsum, Finset.sum_mul]
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_left (hle i) (le_of_lt (hq i))
  · obtain ⟨i, hi⟩ := hlt
    exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hq i)⟩

/-- The explicit maximum/minimum estimates in Lemma 8.3. -/
theorem extreme_weighted_diagonal_bounds (Q : I → I → ℝ) (w : I → ℝ)
    (r : ℝ) (hQ : ∀ i j, 0 < Q i j) (hrow : ∀ i, ∑ j, Q i j = r)
    (hw : ∀ i, 0 < w i) (a b : I)
    (hmax : ∀ i, w i ≤ w a) (hmin : ∀ i, w b ≤ w i)
    (hstrict : w b < w a) :
    w a * (r * w b) < w a * (∑ j, Q a j * w j) ∧
      w b * (∑ j, Q b j * w j) < w a * (r * w b) := by
  constructor
  · exact mul_lt_mul_of_pos_left
      (lt_sum_mul_of_lt (Q a) w (w b) r (hQ a) (hrow a) hmin ⟨a, hstrict⟩)
      (hw a)
  · calc
      w b * (∑ j, Q b j * w j) < w b * (r * w a) :=
        mul_lt_mul_of_pos_left
          (sum_mul_lt_of_lt (Q b) w (w a) r (hQ b) (hrow b) hmax ⟨b, hstrict⟩)
          (hw b)
      _ = w a * (r * w b) := by ring

/-- A positive, nonconstant weight vector gives a nonconstant weighted diagonal
for every entrywise positive matrix with a common row sum. -/
theorem weighted_diagonal_nonconstant [Nonempty I]
    (Q : I → I → ℝ) (w : I → ℝ) (r : ℝ)
    (hQ : ∀ i j, 0 < Q i j) (hrow : ∀ i, ∑ j, Q i j = r)
    (hw : ∀ i, 0 < w i) (hnonconstant : ∃ i j, w i ≠ w j) :
    ∃ a b, w a * (∑ j, Q a j * w j) ≠ w b * (∑ j, Q b j * w j) := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  obtain ⟨b, _, hb⟩ := Finset.exists_min_image Finset.univ w Finset.univ_nonempty
  have hmax : ∀ i, w i ≤ w a := fun i => ha i (Finset.mem_univ i)
  have hmin : ∀ i, w b ≤ w i := fun i => hb i (Finset.mem_univ i)
  have hstrict : w b < w a := by
    apply lt_of_le_of_ne (hmax b)
    intro heq
    obtain ⟨i, j, hij⟩ := hnonconstant
    have hi : w i = w a := le_antisymm (hmax i) (heq ▸ hmin i)
    have hj : w j = w a := le_antisymm (hmax j) (heq ▸ hmin j)
    exact hij (hi.trans hj.symm)
  obtain ⟨hlo, hhi⟩ := extreme_weighted_diagonal_bounds Q w r hQ hrow hw a b
    hmax hmin hstrict
  exact ⟨a, b, ne_of_gt (hhi.trans hlo)⟩

/-- Summing the two diagonal equations gives the same scalar on both sides.
This is the finite-sum trace identity used before the rigidity argument. -/
theorem bipartite_diagonal_constants_eq [Nonempty I]
    (Q : I → I → ℝ) (μ ν : I → ℝ) (cX cY : ℝ)
    (hleft : ∀ i, μ i * (∑ j, Q i j * ν j) = cX)
    (hright : ∀ j, ν j * (∑ i, Q i j * μ i) = cY) : cX = cY := by
  classical
  have hsum : (∑ i, μ i * (∑ j, Q i j * ν j)) =
      ∑ j, ν j * (∑ i, Q i j * μ i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hcard : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  simpa only [hleft, hright, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum

/-- Positive left/right weights satisfying the same constant-diagonal equations
for a strictly positive matrix with equal row and column sums must both be
constant. Symmetry of the matrix is not assumed. -/
theorem bipartite_weights_constant [Nonempty I]
    (Q : I → I → ℝ) (μ ν : I → ℝ) (r c : ℝ)
    (hQ : ∀ i j, 0 < Q i j) (hr : 0 < r)
    (hrow : ∀ i, ∑ j, Q i j = r) (hcol : ∀ j, ∑ i, Q i j = r)
    (hμ : ∀ i, 0 < μ i) (hν : ∀ j, 0 < ν j)
    (hleft : ∀ i, μ i * (∑ j, Q i j * ν j) = c)
    (hright : ∀ j, ν j * (∑ i, Q i j * μ i) = c) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ (∀ i, μ i = a) ∧ (∀ j, ν j = b) := by
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ μ Finset.univ_nonempty
  have hmax : ∀ i, μ i ≤ μ k := fun i => hk i (Finset.mem_univ i)
  have hμconst : ∀ i, μ i = μ k := by
    intro i
    by_contra hne
    have hi : μ i < μ k := lt_of_le_of_ne (hmax i) hne
    have hstrict : ∀ j, c < ν j * (r * μ k) := by
      intro j
      rw [← hright j]
      exact mul_lt_mul_of_pos_left
        (sum_mul_lt_of_lt (fun i => Q i j) μ (μ k) r (fun i => hQ i j)
          (hcol j) hmax ⟨i, hi⟩) (hν j)
    have hsum : (∑ j, Q k j * c) < ∑ j, Q k j * (ν j * (r * μ k)) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun j _ => mul_lt_mul_of_pos_left (hstrict j) (hQ k j))
    have hl : (∑ j, Q k j * c) = r * c := by rw [← Finset.sum_mul, hrow k]
    have hh : (∑ j, Q k j * (ν j * (r * μ k))) = r * c := by
      calc
        (∑ j, Q k j * (ν j * (r * μ k))) = r * (μ k * (∑ j, Q k j * ν j)) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = r * c := by rw [hleft k]
    rw [hl, hh] at hsum
    exact (lt_irrefl _ hsum)
  have hνeq : ∀ j, ν j * (r * μ k) = c := by
    intro j
    have hsum : (∑ i, Q i j * μ i) = r * μ k := by
      simp_rw [hμconst]
      rw [← Finset.sum_mul, hcol j]
    simpa only [hsum] using hright j
  refine ⟨μ k, ν k, hμ k, hν k, hμconst, ?_⟩
  intro j
  exact (mul_right_cancel₀ (ne_of_gt (mul_pos hr (hμ k))))
    ((hνeq j).trans (hνeq k).symm)

/-- The two constant diagonals may initially have different specified values;
the trace identity identifies them, and the weights on each part are constant.
The constants on the two parts need not be equal. -/
theorem bipartite_weights_constant_of_constant_diagonals [Nonempty I]
    (Q : I → I → ℝ) (μ ν : I → ℝ) (r cX cY : ℝ)
    (hQ : ∀ i j, 0 < Q i j) (hr : 0 < r)
    (hrow : ∀ i, ∑ j, Q i j = r) (hcol : ∀ j, ∑ i, Q i j = r)
    (hμ : ∀ i, 0 < μ i) (hν : ∀ j, 0 < ν j)
    (hleft : ∀ i, μ i * (∑ j, Q i j * ν j) = cX)
    (hright : ∀ j, ν j * (∑ i, Q i j * μ i) = cY) :
    cX = cY ∧
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ (∀ i, μ i = a) ∧ (∀ j, ν j = b) := by
  have heq := bipartite_diagonal_constants_eq Q μ ν cX cY hleft hright
  refine ⟨heq, ?_⟩
  apply bipartite_weights_constant Q μ ν r cX hQ hr hrow hcol hμ hν hleft
  intro j
  exact (hright j).trans heq.symm

end PlanarHom.WeightRigidity
