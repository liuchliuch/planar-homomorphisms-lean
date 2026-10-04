import PlanarHom.TraceExponential
import PlanarHom.Boolean
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exponentiating coordinate-local operators on the Boolean cube

Coordinate lifts are explicit ordinary matrices. They are continuous algebra
homomorphisms, distinct lifts commute, and the genuine exponential of their sum
is the actual entrywise tensor product of the two-by-two exponentials.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.CubeTensorExponential
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual tensor matrix indexed by Boolean assignments to all coordinates. -/
def tensor (A : ι → Matrix Bool Bool ℝ) : Matrix (ι → Bool) (ι → Bool) ℝ :=
  fun z w => ∏ r, A r (z r) (w r)

/-- Ordinary tensor multiplication separates into the coordinate products. -/
theorem tensor_mul (A B : ι → Matrix Bool Bool ℝ) :
    tensor A * tensor B = tensor (fun r => A r * B r) := by
  ext z w
  simp only [tensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun r b => A r (z r) b * B r b (w r))).symm

@[simp] theorem tensor_one : tensor (fun _ : ι => (1 : Matrix Bool Bool ℝ)) = 1 := by
  ext z w
  by_cases hzw : z = w
  · subst w; simp [tensor]
  · rw [Matrix.one_apply_ne hzw]
    obtain ⟨r, hr⟩ := Function.ne_iff.mp hzw
    exact Finset.prod_eq_zero (Finset.mem_univ r) (Matrix.one_apply_ne hr)

/-- One coordinate acts by `A`, with genuine identity matrices on all others. -/
def coordinateLift (r : ι) (A : Matrix Bool Bool ℝ) : Matrix (ι → Bool) (ι → Bool) ℝ :=
  fun z w => A (z r) (w r) * ∏ k ∈ Finset.univ.erase r, (1 : Matrix Bool Bool ℝ) (z k) (w k)

/-- The coordinate lift is precisely a tensor with a single nonidentity factor. -/
theorem coordinateLift_eq_tensor (r : ι) (A : Matrix Bool Bool ℝ) :
    coordinateLift r A = tensor (Function.update (fun _ => 1) r A) := by
  ext z w
  unfold coordinateLift tensor
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k => Function.update (fun _ => (1 : Matrix Bool Bool ℝ)) r A k (z k) (w k))
      (Finset.mem_univ r)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

@[simp] theorem coordinateLift_one (r : ι) : coordinateLift r 1 = 1 := by
  rw [coordinateLift_eq_tensor]
  have h : Function.update (fun _ : ι => (1 : Matrix Bool Bool ℝ)) r 1 = fun _ => 1 := by
    funext k
    simp
  rw [h, tensor_one]

@[simp] theorem coordinateLift_add (r : ι) (A B : Matrix Bool Bool ℝ) :
    coordinateLift r (A + B) = coordinateLift r A + coordinateLift r B := by
  ext z w
  simp [coordinateLift, add_mul]

@[simp] theorem coordinateLift_smul (r : ι) (c : ℝ) (A : Matrix Bool Bool ℝ) :
    coordinateLift r (c • A) = c • coordinateLift r A := by
  ext z w
  simp [coordinateLift, smul_eq_mul, mul_assoc]

@[simp] theorem coordinateLift_mul (r : ι) (A B : Matrix Bool Bool ℝ) :
    coordinateLift r (A * B) = coordinateLift r A * coordinateLift r B := by
  simp only [coordinateLift_eq_tensor, tensor_mul]
  congr 1
  funext k
  by_cases hk : k = r
  · subst k; simp
  · simp [Function.update_of_ne hk]

/-- The coordinate lift is an actual real algebra homomorphism. -/
def coordinateLiftAlgHom (r : ι) :
    Matrix Bool Bool ℝ →ₐ[ℝ] Matrix (ι → Bool) (ι → Bool) ℝ where
  toFun := coordinateLift r
  map_one' := coordinateLift_one r
  map_mul' := coordinateLift_mul r
  map_zero' := by ext z w; simp [coordinateLift]
  map_add' := coordinateLift_add r
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, coordinateLift_smul, coordinateLift_one,
      Algebra.algebraMap_eq_smul_one]

/-- Different coordinates commute without requiring their local matrices to commute. -/
theorem coordinateLift_commute (r s : ι) (hrs : r ≠ s) (A B : Matrix Bool Bool ℝ) :
    Commute (coordinateLift r A) (coordinateLift s B) := by
  change coordinateLift r A * coordinateLift s B = coordinateLift s B * coordinateLift r A
  simp only [coordinateLift_eq_tensor, tensor_mul]
  congr 1
  funext k
  by_cases hkr : k = r
  · subst k
    simp [Function.update_of_ne hrs]
  · by_cases hks : k = s
    · subst k
      simp [Function.update_of_ne (Ne.symm hrs)]
    · simp [Function.update_of_ne hkr, Function.update_of_ne hks]

/-- The genuine exponential commutes with coordinate lifting. -/
theorem exp_coordinateLift (r : ι) (A : Matrix Bool Bool ℝ) :
    NormedSpace.exp ℝ (coordinateLift r A) = coordinateLift r (NormedSpace.exp ℝ A) := by
  exact (NormedSpace.map_exp ℝ (coordinateLiftAlgHom r)
    (coordinateLiftAlgHom r).toLinearMap.continuous_of_finiteDimensional A).symm

/-- Exponentiating any partial sum gives the tensor of the chosen coordinate exponentials. -/
theorem exp_sum_coordinateLift (A : ι → Matrix Bool Bool ℝ) (S : Finset ι) :
    NormedSpace.exp ℝ (∑ r ∈ S, coordinateLift r (A r)) =
      tensor (fun r => if r ∈ S then NormedSpace.exp ℝ (A r) else 1) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert r S hr ih =>
    have hc : Commute (coordinateLift r (A r)) (∑ s ∈ S, coordinateLift s (A s)) := by
      apply Commute.sum_right
      intro s hs
      exact coordinateLift_commute r s (by intro heq; subst s; exact hr hs) _ _
    rw [Finset.sum_insert hr, NormedSpace.exp_add_of_commute hc, exp_coordinateLift, ih,
      coordinateLift_eq_tensor, tensor_mul]
    congr 1
    funext k
    by_cases hkr : k = r
    · subst k; simp [hr]
    · simp [Function.update_of_ne hkr, hkr]

/-- The coordinate-local sum exponentiates to an actual tensor product. -/
theorem exp_sum_coordinateLift_eq_tensor (A : ι → Matrix Bool Bool ℝ) :
    NormedSpace.exp ℝ (∑ r, coordinateLift r (A r)) =
      tensor (fun r => NormedSpace.exp ℝ (A r)) := by
  simpa using exp_sum_coordinateLift A Finset.univ

/-- A scalar identity component supplies exactly the scalar exponential factor. -/
theorem exp_scalar_add_sum_coordinateLift (c : ℝ) (A : ι → Matrix Bool Bool ℝ) :
    NormedSpace.exp ℝ (c • (1 : Matrix (ι → Bool) (ι → Bool) ℝ) +
      ∑ r, coordinateLift r (A r)) = Real.exp c • tensor (fun r => NormedSpace.exp ℝ (A r)) := by
  rw [add_comm, TraceExponential.exp_add_smul_one, exp_sum_coordinateLift_eq_tensor]

/-- Entrywise form of the tensor factorization in Proposition 4.8. -/
theorem exp_scalar_add_sum_coordinateLift_entry (c : ℝ) (A : ι → Matrix Bool Bool ℝ)
    (z w : ι → Bool) :
    NormedSpace.exp ℝ (c • (1 : Matrix (ι → Bool) (ι → Bool) ℝ) +
      ∑ r, coordinateLift r (A r)) z w =
      Real.exp c * ∏ r, NormedSpace.exp ℝ (A r) (z r) (w r) := by
  rw [exp_scalar_add_sum_coordinateLift]
  rfl

end PlanarHom.CubeTensorExponential
