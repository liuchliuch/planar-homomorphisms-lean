import PlanarHom.PlanarStretch
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-! Exact ordinary matrix powers from unrestricted internal path colors and
unit internal background. The endpoint colors may coincide, so loops are
covered by exactly the same identity. -/

noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.PathPower
variable {C R : Type*} [Fintype C] [DecidableEq C] [CommSemiring R]

def sourceColor (n : ℕ) (x : C) (τ : Fin n → C) (k : Fin (n+1)) : C :=
  if h : k.val=0 then x else τ ⟨k.val-1,by omega⟩

def targetColor (n : ℕ) (y : C) (τ : Fin n → C) (k : Fin (n+1)) : C :=
  if h : k.val=n then y else τ ⟨k.val,by omega⟩

def weight (n : ℕ) (M : Matrix C C R) (x y : C) (τ : Fin n → C) : R :=
  ∏ k : Fin (n+1), M (sourceColor n x τ k) (targetColor n y τ k)

omit [Fintype C] in
@[simp] theorem weight_zero (M : Matrix C C R) (x y : C) (τ : Fin 0 → C) :
    weight 0 M x y τ = M x y := by simp [weight, sourceColor, targetColor]

omit [Fintype C] in
theorem sourceColor_cons (n : ℕ) (x z : C) (τ : Fin n → C) (k : Fin (n+1)) :
    sourceColor (n+1) x (Fin.cons z τ) k.succ = sourceColor n z τ k := by
  cases k using Fin.cases with
  | zero => simp [sourceColor]
  | succ k =>
    simp only [sourceColor, Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceDIte, Nat.add_sub_cancel]
    exact Fin.cons_succ (α := fun _ : Fin (n+1) => C) z τ k

omit [Fintype C] in
theorem targetColor_cons (n : ℕ) (y z : C) (τ : Fin n → C) (k : Fin (n+1)) :
    targetColor (n+1) y (Fin.cons z τ) k.succ = targetColor n y τ k := by
  by_cases hk : k.val=n
  · simp [targetColor,hk]
  · simp only [targetColor, Fin.val_succ, Nat.add_right_cancel_iff, hk, ↓reduceDIte]
    exact Fin.cons_succ (α := fun _ : Fin (n+1) => C) z τ (⟨k.val,by omega⟩ : Fin n)

theorem weight_cons (n : ℕ) (M : Matrix C C R) (x y z : C) (τ : Fin n → C) :
    weight (n+1) M x y (Fin.cons z τ) = M x z * weight n M z y τ := by
  rw [weight, Fin.prod_univ_succ]
  simp only [sourceColor_cons, targetColor_cons]
  congr 1

/-- Summing all private internal colors yields the ordinary power, for any
finite color space and commutative semiring, with no positivity assumption. -/
theorem sum_weight (n : ℕ) (M : Matrix C C R) (x y : C) :
    (∑ τ : Fin n → C, weight n M x y τ) = (M^(n+1)) x y := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∑ p : C × (Fin n → C), weight (n+1) M x y (Fin.cons p.1 p.2) := by
        apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => C)).symm
        intro τ
        simp
      _ = ∑ z : C, ∑ τ : Fin n → C, M x z * weight n M z y τ := by
        rw [Fintype.sum_prod_type]
        simp only [weight_cons]
      _ = ∑ z : C, M x z * (M^(n+1)) z y := by simp only [← Finset.mul_sum, ih]
      _ = (M^((n+1)+1)) x y := by
        conv_rhs => rw [pow_succ', Matrix.mul_apply]

end PlanarHom.PathPower
