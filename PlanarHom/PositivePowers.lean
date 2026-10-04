import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Positive powers of a connected nonnegative interaction

The off-diagonal positive support of a symmetric real matrix is a simple graph.
If that graph is connected, the matrix is entrywise nonnegative, and all diagonal
entries are positive, every power with exponent at least the number of indices
minus one is entrywise positive. This is the matrix-power positivity step used
in Lemma 3.11 and in the paper's spectral interpolation arguments.

The proof follows a simple support path, whose length is strictly smaller than
the number of vertices, and pads its positive contribution with diagonal steps.
The exponent is an ordinary matrix power, not an entrywise power.
-/

noncomputable section

open scoped BigOperators

namespace PlanarHom.PositivePowers

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The loopless graph of strictly positive entries of a symmetric matrix. -/
def positiveSupport (M : Matrix V V ℝ) (hM : ∀ i j, M i j = M j i) : SimpleGraph V where
  Adj i j := i ≠ j ∧ 0 < M i j
  symm := by
    intro i j h
    exact ⟨h.1.symm, by simpa only [hM j i] using h.2⟩
  loopless := by
    intro i h
    exact h.1 rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem positiveSupport_adj (M : Matrix V V ℝ)
    (hM : ∀ i j, M i j = M j i) (i j : V) :
    (positiveSupport M hM).Adj i j ↔ i ≠ j ∧ 0 < M i j := Iff.rfl

/-- Every ordinary matrix power of an entrywise nonnegative matrix is nonnegative. -/
theorem power_nonneg (M : Matrix V V ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (n : ℕ) (i j : V) : 0 ≤ (M ^ n) i j := by
  induction n generalizing i j with
  | zero =>
    by_cases h : i = j <;> simp [h]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (hM k j)

omit [DecidableEq V] in
/-- A positive summand makes an entry of a product of nonnegative matrices positive. -/
theorem mul_entry_pos (A B : Matrix V V ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    {i j k : V} (hik : 0 < A i k) (hkj : 0 < B k j) :
    0 < (A * B) i j := by
  rw [Matrix.mul_apply]
  exact lt_of_lt_of_le (mul_pos hik hkj)
    (Finset.single_le_sum (fun l _ => mul_nonneg (hA i l) (hB l j))
      (Finset.mem_univ k))

/-- Any walk along positive support edges contributes to a positive matrix-power entry. -/
theorem power_pos_of_walk (M : Matrix V V ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (G : SimpleGraph V) (hG : ∀ ⦃i j⦄, G.Adj i j → 0 < M i j)
    {i j : V} (p : G.Walk i j) : 0 < (M ^ p.length) i j := by
  induction p with
  | nil => simp
  | @cons i k j hik p ih =>
    simpa only [SimpleGraph.Walk.length_cons, pow_succ'] using
      (mul_entry_pos M (M ^ p.length) hM (power_nonneg M hM p.length)
        (hG hik) ih)

/-- Positive diagonal entries allow a positive matrix-power entry to be padded
to every larger exponent. -/
theorem power_pos_of_le (M : Matrix V V ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hdiag : ∀ i, 0 < M i i) {m n : ℕ} {i j : V}
    (hmn : m ≤ n) (hm : 0 < (M ^ m) i j) : 0 < (M ^ n) i j := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction r with
  | zero => simpa using hm
  | succ r ih =>
    simpa only [Nat.add_succ, pow_succ] using
      (mul_entry_pos (M ^ (m + r)) M (power_nonneg M hM (m + r)) hM ih (hdiag j))

/-- Connectivity supplies a simple support path, so `card V - 1` is a uniform
threshold for strict positivity of all matrix-power entries. -/
theorem power_pos_of_connected (M : Matrix V V ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hdiag : ∀ i, 0 < M i i)
    (G : SimpleGraph V) (hedge : ∀ ⦃i j⦄, G.Adj i j → 0 < M i j)
    (hG : G.Connected) {n : ℕ} (hn : Fintype.card V - 1 ≤ n)
    (i j : V) : 0 < (M ^ n) i j := by
  obtain ⟨p, hp⟩ := hG.exists_isPath i j
  have hlen : p.length ≤ Fintype.card V - 1 := Nat.le_sub_one_of_lt hp.length_lt
  exact power_pos_of_le M hM hdiag (hlen.trans hn) (power_pos_of_walk M hM G hedge p)

/-- The paper's matrix-power positivity conclusion, with connectivity expressed
directly using the off-diagonal positive support of the symmetric interaction. -/
theorem power_pos_of_positiveSupport_connected (M : Matrix V V ℝ)
    (hsymm : ∀ i j, M i j = M j i) (hM : ∀ i j, 0 ≤ M i j)
    (hdiag : ∀ i, 0 < M i i) (hconn : (positiveSupport M hsymm).Connected)
    {n : ℕ} (hn : Fintype.card V - 1 ≤ n) (i j : V) : 0 < (M ^ n) i j := by
  exact power_pos_of_connected M hM hdiag (positiveSupport M hsymm)
    (fun {_ _} h => h.2) hconn hn i j

end PlanarHom.PositivePowers
