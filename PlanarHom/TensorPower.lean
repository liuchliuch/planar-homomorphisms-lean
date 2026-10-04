import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Independence of tensor powers

The coordinate model of a pure tensor is indexed by coordinate words of fixed
length. Its entries are products of the entries of the underlying vector.
-/

open scoped BigOperators
open Classical

namespace PlanarHom

/-- The coordinate array of the pure `p`-fold tensor of a vector. -/
def tensorCoordinates {n : ℕ} (p : ℕ) (v : Fin n → ℝ) :
    (Fin p → Fin n) → ℝ := fun a => ∏ k, v (a k)

/-- Nonproportional nonzero vectors admit a separating linear form, given
explicitly by its coordinate coefficients. -/
theorem exists_separating_coefficients {n : ℕ} (u v : Fin n → ℝ)
    (hv : v ≠ 0) (huv : ∀ c : ℝ, u ≠ c • v) :
    ∃ l : Fin n → ℝ, (∑ k, l k * v k) = 0 ∧ (∑ k, l k * u k) ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    apply hv
    funext k
    simpa using not_exists.mp h k
  obtain ⟨t, ht⟩ : ∃ t, v k * u t - v t * u k ≠ 0 := by
    by_contra h
    apply huv (u k / v k)
    funext t
    have ht : v k * u t - v t * u k = 0 := by simpa using not_exists.mp h t
    change u t = u k / v k * v t
    have : u t * v k = u k * v t := by nlinarith
    simpa [div_mul_eq_mul_div] using (eq_div_iff hk).2 this
  let l : Fin n → ℝ := fun z => (if z = t then v k else 0) -
    (if z = k then v t else 0)
  have eval (x : Fin n → ℝ) : (∑ z, l z * x z) = v k * x t - v t * x k := by
    simp [l, sub_mul, Finset.sum_sub_distrib, ite_mul]
  exact ⟨l, by rw [eval]; ring, by rwa [eval]⟩

/-- Contracting a coordinate tensor against a product of linear forms gives
the product of the evaluations of those forms. -/
theorem tensorCoordinates_contract {n p : ℕ}
    (l : Fin p → Fin n → ℝ) (v : Fin n → ℝ) :
    (∑ a : Fin p → Fin n, (∏ k, l k (a k)) * tensorCoordinates p v a) =
      ∏ k, ∑ j, l k j * v j := by
  simp only [tensorCoordinates, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun k j => l k j * v j)).symm

/-- Product forms isolating each vector imply independence of their coordinate
powers. -/
theorem tensorCoordinates_independent_of_separators {n p r : ℕ}
    (v : Fin r → Fin n → ℝ)
    (hsep : ∀ i, ∃ l : Fin p → Fin n → ℝ,
      (∏ k, ∑ a, l k a * v i a) ≠ 0 ∧
      ∀ j, j ≠ i → (∏ k, ∑ a, l k a * v j a) = 0) :
    LinearIndependent ℝ (fun i => tensorCoordinates p (v i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  obtain ⟨l, hli, hlj⟩ := hsep i
  have hcoord (a : Fin p → Fin n) :
      (∑ j, c j * tensorCoordinates p (v j) a) = 0 := by
    have h := congrFun hc a
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  have hz : (∑ j, c j * (∏ k, ∑ a, l k a * v j a)) = 0 := by
    simp_rw [← tensorCoordinates_contract]
    calc
      (∑ j, c j * ∑ a, (∏ k, l k (a k)) * tensorCoordinates p (v j) a) =
          ∑ a, (∏ k, l k (a k)) *
            (∑ j, c j * tensorCoordinates p (v j) a) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by simp_rw [hcoord, mul_zero]; exact Finset.sum_const_zero
  have hi : c i * (∏ k, ∑ a, l k a * v i a) = 0 := by
    rw [Finset.sum_eq_single i] at hz
    · exact hz
    · intro j _ hji
      rw [hlj j hji, mul_zero]
    · simp
  exact (mul_eq_zero.mp hi).resolve_right hli

/-- The sharp tensor-power independence result for at least two vectors. -/
theorem tensorCoordinates_linearIndependent_succ {n r : ℕ}
    (v : Fin (r + 2) → Fin n → ℝ)
    (hnonzero : ∀ i, v i ≠ 0)
    (hproj : ∀ i j, i ≠ j → ∀ c : ℝ, v i ≠ c • v j) :
    LinearIndependent ℝ (fun i => tensorCoordinates (r + 1) (v i)) := by
  apply tensorCoordinates_independent_of_separators
  intro i
  have hs (k : Fin (r + 1)) := exists_separating_coefficients
    (v i) (v (i.succAbove k)) (hnonzero _) (hproj _ _ (Fin.ne_succAbove _ _))
  choose l hlzero hlne using hs
  refine ⟨l, Finset.prod_ne_zero_iff.mpr (fun k _ => hlne k), ?_⟩
  intro j hji
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simpa only [hk] using hlzero k

/-- Lemma 3.6, in coordinates: at the exponent `max 1 (r - 1)`,
nonzero pairwise nonproportional real vectors have independent powers. -/
theorem tensorCoordinates_linearIndependent {n r : ℕ}
    (v : Fin r → Fin n → ℝ)
    (hnonzero : ∀ i, v i ≠ 0)
    (hproj : ∀ i j, i ≠ j → ∀ c : ℝ, v i ≠ c • v j) :
    LinearIndependent ℝ (fun i => tensorCoordinates (max 1 (r - 1)) (v i)) := by
  cases r with
  | zero => exact linearIndependent_empty_type
  | succ r =>
    cases r with
    | zero =>
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h : c i • v i = 0 := by
        funext a
        have he := congrFun hc (fun _ => a)
        simpa [tensorCoordinates, Fin.sum_univ_one, Subsingleton.elim (0 : Fin 1) i] using he
      exact (smul_eq_zero.mp h).resolve_right (hnonzero i)
    | succ r =>
      have hp : max 1 ((r + 1 + 1) - 1) = r + 1 := by omega
      change LinearIndependent ℝ
        (fun i => tensorCoordinates (max 1 ((r + 1 + 1) - 1)) (v i))
      rw [hp]
      exact tensorCoordinates_linearIndependent_succ v hnonzero hproj

/-- The weighted Gram identity for pure tensor coordinates. -/
theorem tensorCoordinates_weighted_gram {n p : ℕ}
    (d u v : Fin n → ℝ) :
    (∑ k, d k * u k * v k) ^ p =
      ∑ a : Fin p → Fin n, (∏ k, d (a k)) *
        tensorCoordinates p u a * tensorCoordinates p v a := by
  calc
    (∑ k, d k * u k * v k) ^ p =
        ∏ _ : Fin p, ∑ k, d k * u k * v k := by simp
    _ = ∑ a : Fin p → Fin n, ∏ k, d (a k) * u (a k) * v (a k) :=
      Fintype.prod_sum (fun _ k => d k * u k * v k)
    _ = _ := by simp only [Finset.prod_mul_distrib, tensorCoordinates]

/-- The quadratic form of the weighted Hadamard Gram power is a positive
weighted sum of squares of coordinate combinations. -/
theorem tensorCoordinates_weighted_quadratic {n p r : ℕ}
    (d : Fin n → ℝ) (v : Fin r → Fin n → ℝ) (c : Fin r → ℝ) :
    (∑ i, ∑ j, c i * (∑ k, d k * v i k * v j k) ^ p * c j) =
      ∑ a : Fin p → Fin n, (∏ k, d (a k)) *
        (∑ i, c i * tensorCoordinates p (v i) a) ^ 2 := by
  simp_rw [tensorCoordinates_weighted_gram, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The positive-definite conclusion of Lemma 3.6, stated directly as
strict positivity of the associated real quadratic form. -/
theorem tensorCoordinates_weighted_quadratic_pos {n r : ℕ}
    (d : Fin n → ℝ) (hd : ∀ k, 0 < d k)
    (v : Fin r → Fin n → ℝ)
    (hnonzero : ∀ i, v i ≠ 0)
    (hproj : ∀ i j, i ≠ j → ∀ t : ℝ, v i ≠ t • v j)
    (c : Fin r → ℝ) (hc : c ≠ 0) :
    0 < ∑ i, ∑ j, c i *
      (∑ k, d k * v i k * v j k) ^ (max 1 (r - 1)) * c j := by
  rw [tensorCoordinates_weighted_quadratic]
  have hind := tensorCoordinates_linearIndependent v hnonzero hproj
  have hcomb : (∑ i, c i • tensorCoordinates (max 1 (r - 1)) (v i)) ≠ 0 := by
    intro hz
    apply hc
    exact funext (Fintype.linearIndependent_iff.mp hind c hz)
  obtain ⟨a, ha⟩ : ∃ a, (∑ i, c i *
      tensorCoordinates (max 1 (r - 1)) (v i) a) ≠ 0 := by
    by_contra h
    apply hcomb
    funext a
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      using not_ne_iff.mp (not_exists.mp h a)
  apply Finset.sum_pos'
  · intro b _
    exact mul_nonneg (Finset.prod_nonneg (fun k _ => (hd (b k)).le)) (sq_nonneg _)
  · exact ⟨a, Finset.mem_univ a,
      mul_pos (Finset.prod_pos (fun k _ => hd (a k))) (sq_pos_of_ne_zero ha)⟩

/-- The canonical linear coordinate map from the actual tensor power to
coordinate arrays. Its construction uses the universal property of the tensor
product and coordinate evaluation in each factor. -/
noncomputable def tensorCoordinateMap (n p : ℕ) :
    TensorPower ℝ p (Fin n → ℝ) →ₗ[ℝ] ((Fin p → Fin n) → ℝ) :=
  LinearMap.pi fun a => PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℝ (Fin p) ℝ).compLinearMap
      (fun k => LinearMap.proj (a k)))

/-- The coordinates used above are exactly the image of the usual pure tensor. -/
@[simp] theorem tensorCoordinateMap_pure {n p : ℕ} (v : Fin n → ℝ) :
    tensorCoordinateMap n p (PiTensorProduct.tprod ℝ (fun _ : Fin p => v)) =
      tensorCoordinates p v := by
  ext a
  simp [tensorCoordinateMap, tensorCoordinates, MultilinearMap.mkPiAlgebra_apply]

/-- Lemma 3.6 for mathlib's actual tensor powers. -/
theorem tensorPower_linearIndependent {n r : ℕ}
    (v : Fin r → Fin n → ℝ)
    (hnonzero : ∀ i, v i ≠ 0)
    (hproj : ∀ i j, i ≠ j → ∀ c : ℝ, v i ≠ c • v j) :
    LinearIndependent ℝ (fun i => PiTensorProduct.tprod ℝ
      (fun _ : Fin (max 1 (r - 1)) => v i)) := by
  apply LinearIndependent.of_comp (tensorCoordinateMap n (max 1 (r - 1)))
  simpa only [Function.comp_def, tensorCoordinateMap_pure]
    using tensorCoordinates_linearIndependent v hnonzero hproj

/-- Weighted tensor Gram matrices are positive definite, with the exponent
prescribed in Lemma 3.6. -/
theorem weighted_tensor_gram_posDef {n r : ℕ}
    (d : Fin n → ℝ) (hd : ∀ k, 0 < d k)
    (v : Fin r → Fin n → ℝ)
    (hnonzero : ∀ i, v i ≠ 0)
    (hproj : ∀ i j, i ≠ j → ∀ t : ℝ, v i ≠ t • v j) :
    Matrix.PosDef (fun i j => (∑ k, d k * v i k * v j k) ^ (max 1 (r - 1))) := by
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  · intro c hc
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc] using
      tensorCoordinates_weighted_quadratic_pos d hd v hnonzero hproj c hc

/-- The matrix formulation of the consequence in Lemma 3.6:
`(B * diagonal d * Bᵀ)` raised entrywise to `max 1 (r - 1)` is positive definite.
No sign condition on entries of `B` is assumed. -/
theorem hadamard_weighted_gram_posDef {n r : ℕ}
    (B : Matrix (Fin r) (Fin n) ℝ) (d : Fin n → ℝ) (hd : ∀ k, 0 < d k)
    (hnonzero : ∀ i, B i ≠ 0)
    (hproj : ∀ i j, i ≠ j → ∀ t : ℝ, B i ≠ t • B j) :
    Matrix.PosDef (fun i j =>
      ((B * Matrix.diagonal d * B.transpose) i j) ^ (max 1 (r - 1))) := by
  have he : B * Matrix.diagonal d * B.transpose =
      fun i j => ∑ k, d k * B i k * B j k := by
    ext i j
    change (∑ k, (B * Matrix.diagonal d) i k * B j k) = _
    simp only [Matrix.mul_diagonal]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  exact weighted_tensor_gram_posDef d hd B hnonzero hproj

end PlanarHom
