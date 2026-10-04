import Mathlib.LinearAlgebra.Vandermonde

/-!
# Exact finite moment uniqueness

The Vandermonde argument used in Sections 8, 9, and 11 recovers one coefficient
for each distinct numerical base from the first `n` moments. The coefficients
need not be positive. This file also proves the shifted-power version used in
Lemma 3.1: for distinct nonzero bases, the powers `1, ..., n` determine all
coefficients, even when bases or coefficients have signs.

These are algebraic uniqueness statements. They do not assert a complexity
bound for constructing the bases or solving an interpolation system.
-/

open scoped BigOperators

namespace PlanarHom

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}

/-- The first `n` moments at `n` distinct bases determine every coefficient.
This includes `n = 0`, and zero bases are allowed. -/
theorem finite_moment_unique {δ a b : Fin n → R}
    (hδ : Function.Injective δ)
    (h : ∀ t : Fin n, (∑ j, a j * δ j ^ (t : ℕ)) =
      ∑ j, b j * δ j ^ (t : ℕ)) : a = b := by
  have hz : (fun j => a j - b j) = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hδ fun t => by
      simp only [sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (h t)
  funext j
  exact sub_eq_zero.mp (congrFun hz j)

/-- Equality of the finite moment vectors is equivalent to coefficientwise
equality. -/
theorem finite_moment_eq_iff {δ a b : Fin n → R}
    (hδ : Function.Injective δ) :
    (∀ t : Fin n, (∑ j, a j * δ j ^ (t : ℕ)) =
      ∑ j, b j * δ j ^ (t : ℕ)) ↔ a = b := by
  constructor
  · exact finite_moment_unique hδ
  · rintro rfl t
    rfl

/-- If two coefficient vectors differ, one of the first `n` moments detects
the difference. This is the finite witness needed in the moment arguments. -/
theorem exists_moment_ne_of_ne {δ a b : Fin n → R}
    (hδ : Function.Injective δ) (hab : a ≠ b) :
    ∃ t : Fin n, (∑ j, a j * δ j ^ (t : ℕ)) ≠
      ∑ j, b j * δ j ^ (t : ℕ) := by
  classical
  by_contra h
  apply hab
  apply finite_moment_unique hδ
  intro t
  by_contra ht
  exact h ⟨t, ht⟩

/-- A common shift of the powers preserves uniqueness when every base is
nonzero. No order or positivity hypothesis is used. -/
theorem shifted_finite_moment_unique {δ a b : Fin n → R} (k : ℕ)
    (hδ : Function.Injective δ) (hzero : ∀ j, δ j ≠ 0)
    (h : ∀ t : Fin n, (∑ j, a j * δ j ^ ((t : ℕ) + k)) =
      ∑ j, b j * δ j ^ ((t : ℕ) + k)) : a = b := by
  have hscaled : (fun j => a j * δ j ^ k) = (fun j => b j * δ j ^ k) := by
    apply finite_moment_unique hδ
    intro t
    simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using h t
  funext j
  exact mul_right_cancel₀ (pow_ne_zero k (hzero j)) (congrFun hscaled j)

/-- Lemma 3.1's exact interpolation uniqueness: samples with exponents
`1, ..., n` determine the coefficients of distinct nonzero bases. -/
theorem positive_power_interpolation_unique {δ a b : Fin n → R}
    (hδ : Function.Injective δ) (hzero : ∀ j, δ j ≠ 0)
    (h : ∀ t : Fin n, (∑ j, a j * δ j ^ ((t : ℕ) + 1)) =
      ∑ j, b j * δ j ^ ((t : ℕ) + 1)) : a = b :=
  shifted_finite_moment_unique 1 hδ hzero h

/-- Once the positive-power samples agree, any desired linear combination of
the recovered coefficients agrees. In Lemma 3.1, `θ` is the prescribed map on
the distinct products. -/
theorem interpolation_target_eq {δ a b : Fin n → R}
    (hδ : Function.Injective δ) (hzero : ∀ j, δ j ≠ 0)
    (h : ∀ t : Fin n, (∑ j, a j * δ j ^ ((t : ℕ) + 1)) =
      ∑ j, b j * δ j ^ ((t : ℕ) + 1)) (θ : R → R) :
    (∑ j, a j * θ (δ j)) = ∑ j, b j * θ (δ j) := by
  rw [positive_power_interpolation_unique hδ hzero h]

/-- If each of the first `n` moments is constant across a family of classes,
then each coefficient is constant across those classes. The coefficients can
represent multiplicities or sums of background vertex weights. -/
theorem coefficients_constant_of_moments_constant {S : Type*}
    {δ : Fin n → R} {p : S → Fin n → R} (hδ : Function.Injective δ)
    (h : ∀ s s' (t : Fin n), (∑ j, p s j * δ j ^ (t : ℕ)) =
      ∑ j, p s' j * δ j ^ (t : ℕ)) :
    ∀ s s' j, p s j = p s' j := by
  intro s s' j
  exact congrFun (finite_moment_unique hδ (h s s')) j

end PlanarHom
