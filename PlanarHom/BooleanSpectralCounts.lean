import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum

/-! Finite Boolean branch counts for the grouping step of Theorem 5.1.
The identities require only a commutative monoid. In particular, branch values
may coincide or vanish, and every coordinate is counted with its multiplicity. -/

open scoped BigOperators

namespace PlanarHom.BooleanSpectralCounts

variable {d b m : ℕ}

/-- The number of coordinates assigned to a class. -/
def multiplicity (cls : Fin d → Fin b) (g : Fin b) : ℕ :=
  (Finset.univ.filter (fun i => cls i = g)).card

/-- The total number of edge-coordinate occurrences in a class. -/
def total (cls : Fin d → Fin b) (m : ℕ) (g : Fin b) : ℕ :=
  multiplicity cls g * m

/-- The number of minus-branch occurrences in a class. -/
def count (cls : Fin d → Fin b) (choice : Fin m → Fin d → Bool) (g : Fin b) : ℕ :=
  (Finset.univ.filter (fun p : Fin m × Fin d => cls p.2 = g ∧ choice p.1 p.2 = true)).card

theorem class_card (cls : Fin d → Fin b) (m : ℕ) (g : Fin b) :
    (Finset.univ.filter (fun p : Fin m × Fin d => cls p.2 = g)).card = total cls m g := by
  rw [← Finset.univ_product_univ, Finset.filter_product_right (fun i : Fin d => cls i = g), Finset.card_product]
  simp [total, multiplicity, Nat.mul_comm]

theorem count_le_total (cls : Fin d → Fin b) (choice : Fin m → Fin d → Bool)
    (g : Fin b) : count cls choice g ≤ total cls m g := by
  rw [count, ← class_card cls m g]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact hp.1

/-- The literal count as an index of the finite grouped interpolation grid. -/
def countIndex (cls : Fin d → Fin b) (choice : Fin m → Fin d → Bool)
    (g : Fin b) : Fin (total cls m g + 1) :=
  ⟨count cls choice g, Nat.lt_succ_of_le (count_le_total cls choice g)⟩

@[simp] theorem countIndex_val (cls : Fin d → Fin b)
    (choice : Fin m → Fin d → Bool) (g : Fin b) :
    (countIndex cls choice g).val = count cls choice g := rfl

@[simp] theorem total_zero (cls : Fin d → Fin b) (g : Fin b) :
    total cls 0 g = 0 := by simp [total]

@[simp] theorem count_no_edges (cls : Fin d → Fin b)
    (choice : Fin 0 → Fin d → Bool) (g : Fin b) : count cls choice g = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa using count_le_total cls choice g)

theorem count_eq_zero_of_multiplicity_eq_zero (cls : Fin d → Fin b)
    (choice : Fin m → Fin d → Bool) (g : Fin b) (h : multiplicity cls g = 0) :
    count cls choice g = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa [total, h] using count_le_total cls choice g)

/-- A finite Boolean product records only the number of true choices. -/
theorem prod_bool_eq {I R : Type*} [DecidableEq I] [CommMonoid R]
    (s : Finset I) (choice : I → Bool) (plus minus : R) :
    (∏ i ∈ s, if choice i then minus else plus) =
      plus ^ (s.card - (s.filter (fun i => choice i = true)).card) *
        minus ^ (s.filter (fun i => choice i = true)).card := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hcard := Finset.filter_card_add_filter_neg_card_eq_card
    (s := s) (fun i => choice i = true)
  have hfalse : (s.filter (fun i => ¬choice i = true)).card =
      s.card - (s.filter (fun i => choice i = true)).card := by omega
  rw [hfalse, mul_comm]

theorem class_product_eq {R : Type*} [CommMonoid R]
    (cls : Fin d → Fin b) (choice : Fin m → Fin d → Bool)
    (plus minus : Fin b → R) (g : Fin b) :
    (∏ p ∈ Finset.univ.filter (fun p : Fin m × Fin d => cls p.2 = g),
      if choice p.1 p.2 then minus (cls p.2) else plus (cls p.2)) =
      plus g ^ (total cls m g - count cls choice g) * minus g ^ count cls choice g := by
  calc
    _ = ∏ p ∈ Finset.univ.filter (fun p : Fin m × Fin d => cls p.2 = g),
        if choice p.1 p.2 then minus g else plus g := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := by
      rw [prod_bool_eq, class_card]
      simp only [Finset.filter_filter, count]

/-- Exact rearrangement by class and Boolean count, with no cancellation. -/
theorem product_eq_grouped {R : Type*} [CommMonoid R]
    (cls : Fin d → Fin b) (choice : Fin m → Fin d → Bool)
    (plus minus : Fin b → R) :
    (∏ e, ∏ i, if choice e i then minus (cls i) else plus (cls i)) =
      ∏ g, plus g ^ (total cls m g - count cls choice g) * minus g ^ count cls choice g := by
  rw [← Finset.prod_product', Finset.univ_product_univ]
  rw [← Finset.prod_fiberwise Finset.univ (fun p : Fin m × Fin d => cls p.2)]
  exact Finset.prod_congr rfl (fun g _ => class_product_eq cls choice plus minus g)

/-- Replacing every factor outside one retained class by one leaves its count. -/
theorem retained_product_eq {R : Type*} [CommMonoid R]
    (cls : Fin d → Fin b) (choice : Fin m → Fin d → Bool)
    (plus minus : Fin b → R) (g : Fin b) :
    (∏ e, ∏ i, if cls i = g then
      (if choice e i then minus (cls i) else plus (cls i)) else 1) =
      plus g ^ (total cls m g - count cls choice g) * minus g ^ count cls choice g := by
  rw [← Finset.prod_product', Finset.univ_product_univ, ← Finset.prod_filter]
  exact class_product_eq cls choice plus minus g

/-- Two branch choices with the same retained count have the same retained product. -/
theorem retained_product_eq_of_count_eq {R : Type*} [CommMonoid R]
    (cls : Fin d → Fin b) (choice₁ choice₂ : Fin m → Fin d → Bool)
    (plus minus : Fin b → R) (g : Fin b)
    (h : count cls choice₁ g = count cls choice₂ g) :
    (∏ e, ∏ i, if cls i = g then
      (if choice₁ e i then minus (cls i) else plus (cls i)) else 1) =
    (∏ e, ∏ i, if cls i = g then
      (if choice₂ e i then minus (cls i) else plus (cls i)) else 1) := by
  rw [retained_product_eq, retained_product_eq, h]

end PlanarHom.BooleanSpectralCounts
