import PlanarHom.Moments
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Exact finite interpolation reconstruction

The algebraic recovery map in Lemma 3.1 and equation (3.8): queries at positive
integer powers recover merged coefficients, then any well-defined target
product is evaluated. This is exact field algebra. A polynomial-time bit-machine
implementation and planar query-generation proof are separate obligations.
-/

open scoped BigOperators
open Matrix
open Classical
noncomputable section

namespace PlanarHom.Interpolation

variable {K : Type*} [Field K] {n : ℕ}

/-- Rows correspond to query exponents 1,...,n and columns to distinct bases. -/
def shiftedVandermonde (μ : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  (Matrix.vandermonde μ).transpose * Matrix.diagonal μ

@[simp] theorem shiftedVandermonde_apply (μ : Fin n → K) (i j : Fin n) :
    shiftedVandermonde μ i j = μ j ^ (i.val + 1) := by
  simp [shiftedVandermonde, Matrix.mul_diagonal, Matrix.transpose_apply, pow_succ]

theorem shiftedVandermonde_det (μ : Fin n → K) :
    (shiftedVandermonde μ).det =
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (μ j - μ i)) * ∏ i, μ i := by
  rw [shiftedVandermonde, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_vandermonde, Matrix.det_diagonal]

theorem shiftedVandermonde_det_ne_zero (μ : Fin n → K)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0) :
    (shiftedVandermonde μ).det ≠ 0 := by
  rw [shiftedVandermonde, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hμ)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hzero i))

/-- Exact vector of oracle values at the positive integer exponents. -/
def queryValues (μ a : Fin n → K) : Fin n → K :=
  fun h => ∑ j, a j * μ j ^ (h.val + 1)

theorem queryValues_eq_mulVec (μ a : Fin n → K) :
    queryValues μ a = (shiftedVandermonde μ).mulVec a := by
  funext h
  simp only [queryValues, Matrix.mulVec, dotProduct, shiftedVandermonde_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Algebraic recovery from the finite query vector. -/
noncomputable def recoverCoefficients (μ y : Fin n → K) : Fin n → K :=
  (shiftedVandermonde μ)⁻¹.mulVec y

theorem recover_queryValues (μ a : Fin n → K)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0) :
    recoverCoefficients μ (queryValues μ a) = a := by
  rw [recoverCoefficients, queryValues_eq_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (shiftedVandermonde_det_ne_zero μ hμ hzero)), Matrix.one_mulVec]

/-- Replace each recovered source-product class by its specified target weight. -/
noncomputable def evaluateTarget (μ target y : Fin n → K) : K :=
  ∑ j, target j * recoverCoefficients μ y j

/-- The exact finite-query reconstruction formula, with signed coefficients
and signed nonzero distinct bases allowed. -/
theorem evaluateTarget_queryValues (μ target a : Fin n → K)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0) :
    evaluateTarget μ target (queryValues μ a) = ∑ j, target j * a j := by
  rw [evaluateTarget, recover_queryValues μ a hμ hzero]

/-- The reconstruction depends only on the observed query vector. -/
theorem evaluateTarget_of_queries (μ target a y : Fin n → K)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0)
    (hy : ∀ h, y h = ∑ j, a j * μ j ^ (h.val + 1)) :
    evaluateTarget μ target y = ∑ j, target j * a j := by
  have : y = queryValues μ a := funext hy
  rw [this, evaluateTarget_queryValues μ target a hμ hzero]

/-- Merge assignments with the same source product into one coefficient. -/
def classCoefficients {A : Type*} [Fintype A] (classOf : A → Fin n) (rest : A → K) :
    Fin n → K := fun j => ∑ a : {a // classOf a = j}, rest a.1

/-- The finite fiber-sum identity retains every unchanged signed factor. -/
theorem sum_classCoefficients {A : Type*} [Fintype A]
    (classOf : A → Fin n) (rest : A → K) (target : Fin n → K) :
    (∑ j, target j * classCoefficients classOf rest j) =
      ∑ a, target (classOf a) * rest a := by
  rw [← Fintype.sum_fiberwise classOf (fun a => target (classOf a) * rest a)]
  apply Finset.sum_congr rfl
  intro j _
  rw [classCoefficients, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [a.property]

/-- The actual positive-power query sum has the merged coefficient expansion. -/
theorem grouped_queryValues {A : Type*} [Fintype A]
    (classOf : A → Fin n) (rest : A → K) (μ : Fin n → K) (h : Fin n) :
    (∑ a, rest a * μ (classOf a) ^ (h.val + 1)) =
      queryValues μ (classCoefficients classOf rest) h := by
  simpa only [queryValues, mul_comm] using
    (sum_classCoefficients classOf rest (fun j => μ j ^ (h.val + 1))).symm

/-- Finite oracle-value identity at the algebraic heart of Lemmas 3.1/A.3.
Assignments sharing a source product are grouped once; querying powers 1..n
then recovers any replacement depending only on that product class.

This theorem does not assert the polynomial class-count or bit-cost bounds. -/
theorem evaluateTarget_grouped_queries {A : Type*} [Fintype A]
    (classOf : A → Fin n) (rest : A → K) (μ target : Fin n → K)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0) :
    evaluateTarget μ target
      (fun h => ∑ a, rest a * μ (classOf a) ^ (h.val + 1)) =
      ∑ a, target (classOf a) * rest a := by
  have hy : (fun h => ∑ a, rest a * μ (classOf a) ^ (h.val + 1)) =
      queryValues μ (classCoefficients classOf rest) := by
    funext h
    exact grouped_queryValues classOf rest μ h
  rw [hy, evaluateTarget_queryValues μ target _ hμ hzero,
    sum_classCoefficients]

end PlanarHom.Interpolation
