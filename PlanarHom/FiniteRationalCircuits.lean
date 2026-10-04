import PlanarHom.RationalCircuits
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Compiling fixed finite sums, products, determinants and Cramer coordinates -/
namespace PlanarHom.FiniteRationalCircuits
open Complexity ArithmeticCircuitPrimitives RationalCircuits BinaryArithmetic
open scoped BigOperators

/-- The finite index set is fixed program data, never an unbounded transition. -/
theorem fp_sum {α ι : Type} (ea : BitEncoding α) (s : Finset ι) (f : α→ι→ℚ)
    (hf : ∀ i, FP ea BitEncoding.rat (fun a => f a i)) :
    FP ea BitEncoding.rat (fun a => ∑ i ∈ s, f a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fp_const ea BitEncoding.rat 0
  | @insert i s hi ih =>
    exact (((hf i).pair ih).comp fp_rational_addition).congr
      (fun a => by simp [Finset.sum_insert,hi])

theorem fp_prod {α ι : Type} (ea : BitEncoding α) (s : Finset ι) (f : α→ι→ℚ)
    (hf : ∀ i, FP ea BitEncoding.rat (fun a => f a i)) :
    FP ea BitEncoding.rat (fun a => ∏ i ∈ s, f a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fp_const ea BitEncoding.rat 1
  | @insert i s hi ih =>
    exact (((hf i).pair ih).comp fp_rational_multiplication).congr
      (fun a => by simp [Finset.prod_insert,hi])

/-- The determinant's finite Leibniz expansion is an actual rational circuit. -/
theorem fp_det {α ι : Type} [Fintype ι] [DecidableEq ι]
    (ea : BitEncoding α) (M : α→Matrix ι ι ℚ)
    (hM : ∀ i j, FP ea BitEncoding.rat (fun a => M a i j)) :
    FP ea BitEncoding.rat (fun a => (M a).det) := by
  classical
  have hprod (σ : Equiv.Perm ι) := fp_prod ea Finset.univ (fun a i => M a (σ i) i) (fun i => hM (σ i) i)
  have hterm (σ : Equiv.Perm ι) :=
    ((fp_const ea BitEncoding.rat (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ)).pair (hprod σ)).comp
      fp_rational_multiplication
  exact (fp_sum ea Finset.univ (fun a σ => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) *
    ∏ i, M a (σ i) i) hterm).congr (fun a => by rw [Matrix.det_apply'])

theorem fp_cramer {α ι : Type} [Fintype ι] [DecidableEq ι]
    (ea : BitEncoding α) (M : α→Matrix ι ι ℚ) (b : α→ι→ℚ)
    (hM : ∀ i j, FP ea BitEncoding.rat (fun a => M a i j))
    (hb : ∀ i, FP ea BitEncoding.rat (fun a => b a i)) (i : ι) :
    FP ea BitEncoding.rat (fun a => Matrix.cramer (M a) (b a) i) := by
  have hm : ∀ j k, FP ea BitEncoding.rat (fun a => ((M a).updateCol i (b a)) j k) := by
    intro j k
    by_cases h : k=i
    · simpa [Matrix.updateCol_apply,h] using hb j
    · simpa [Matrix.updateCol_apply,h] using hM j k
  exact (fp_det ea (fun a => (M a).updateCol i (b a)) hm).congr (fun a => (Matrix.cramer_apply _ _ _).symm)

/-- A fixed finite conjunction is compiled from two-input finite Boolean gates. -/
theorem fp_all {α ι : Type} (ea : BitEncoding α) (s : Finset ι) (f : α→ι→Bool)
    (hf : ∀ i, FP ea BitEncoding.bool (fun a => f a i)) :
    FP ea BitEncoding.bool (fun a => decide (∀ i ∈ s, f a i=true)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fp_const ea BitEncoding.bool true
  | @insert i s hi ih =>
    exact (((hf i).pair ih).comp (fp_bool_gate (fun p => p.1 && p.2))).congr
      (fun a => by simp)

end PlanarHom.FiniteRationalCircuits
