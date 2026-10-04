import PlanarHom.PowerRootLiftMatrix
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Fixed tensor sums and sums of matrix eigenvalues

The rational matrix constructed here has every sum of a fixed number of
eigenvalues of the input matrix as an eigenvalue. Repetitions are allowed.
-/

noncomputable section
namespace PlanarHom.TensorSumEigenvalues
open scoped BigOperators Kronecker
open Matrix

universe u
def Index (J : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => J × Index J n

instance {J : Type*} [Fintype J] (n : ℕ) : Fintype (Index J n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (J × Index J n))

instance {J : Type*} [DecidableEq J] (n : ℕ) : DecidableEq (Index J n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => exact inferInstanceAs (DecidableEq (J × Index J n))

theorem card_index {J : Type*} [Fintype J] (n : ℕ) :
    Fintype.card (Index J n) = Fintype.card J ^ n := by
  induction n with
  | zero => simp [Index]
  | succ n ih =>
    change Fintype.card (J × Index J n) = _
    rw [Fintype.card_prod, ih, pow_succ]
    exact Nat.mul_comm _ _

variable {R : Type*} [CommRing R] {J : Type*} [Fintype J] [DecidableEq J]

def matrix : (n : ℕ) → Matrix J J R → Matrix (Index J n) (Index J n) R
  | 0, _ => 0
  | n+1, A => A ⊗ₖ (1 : Matrix (Index J n) (Index J n) R) +
      (1 : Matrix J J R) ⊗ₖ matrix n A

def vector {I H : Type*} (u : I → R) (v : H → R) : I × H → R :=
  fun p => u p.1 * v p.2

theorem kronecker_mulVec_vector {I H : Type*} [Fintype I] [Fintype H]
    (A : Matrix I I R) (B : Matrix H H R) (u : I → R) (v : H → R) :
    (A ⊗ₖ B) *ᵥ vector u v = vector (A *ᵥ u) (B *ᵥ v) := by
  funext p
  simp only [Matrix.mulVec, dotProduct, vector, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem kronecker_sum_eigen {I H : Type*} [Fintype I] [Fintype H]
    [DecidableEq I] [DecidableEq H]
    (A : Matrix I I R) (B : Matrix H H R) (u : I → R) (v : H → R)
    (r s : R) (hu : A *ᵥ u = r • u) (hv : B *ᵥ v = s • v) :
    (A ⊗ₖ 1 + 1 ⊗ₖ B) *ᵥ vector u v = (r+s) • vector u v := by
  rw [Matrix.add_mulVec, kronecker_mulVec_vector, kronecker_mulVec_vector,
    Matrix.one_mulVec, Matrix.one_mulVec, hu, hv]
  funext p
  simp only [vector, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem vector_ne_zero {K : Type*} [Field K] {I H : Type*}
    (u : I → K) (v : H → K) (hu : u ≠ 0) (hv : v ≠ 0) : vector u v ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  intro h
  have he := congrFun h (i,j)
  exact mul_ne_zero hi hj he

theorem eigenvalues_sum {K : Type*} [Field K] (A : Matrix J J K) (rs : List K)
    (h : ∀ r ∈ rs, ∃ v : J → K, v ≠ 0 ∧ A *ᵥ v = r • v) :
    ∃ v : Index J rs.length → K, v ≠ 0 ∧ matrix rs.length A *ᵥ v = rs.sum • v := by
  induction rs with
  | nil =>
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro hz
      have he := congrFun hz PUnit.unit
      exact one_ne_zero he
    · simp [matrix]
  | cons r rs ih =>
    obtain ⟨u, hu, he⟩ := h r (by simp)
    obtain ⟨v, hv, hf⟩ := ih (fun s hs => h s (by simp [hs]))
    refine ⟨vector u v, vector_ne_zero u v hu hv, ?_⟩
    exact kronecker_sum_eigen A (matrix rs.length A) u v r rs.sum he hf

theorem charpoly_sum_roots {K : Type*} [Field K] (A : Matrix J J K) (rs : List K)
    (h : ∀ r ∈ rs, ∃ v : J → K, v ≠ 0 ∧ A *ᵥ v = r • v) :
    (matrix rs.length A).charpoly.eval rs.sum = 0 := by
  obtain ⟨v, hv, he⟩ := eigenvalues_sum A rs h
  exact PowerRootLiftMatrix.charpoly_eval_zero_of_eigen _ _ v hv he

theorem matrix_map {S : Type*} [CommRing S] (f : R →+* S)
    (n : ℕ) (A : Matrix J J R) :
    (matrix n A).map f = matrix n (A.map f) := by
  induction n with
  | zero => ext i j; simp [matrix]
  | succ n ih =>
    ext i j
    by_cases h₁ : i.1 = j.1 <;> by_cases h₂ : i.2 = j.2 <;>
      simp [matrix, Matrix.kroneckerMap_apply, Matrix.one_apply, ← ih, h₁, h₂]

end PlanarHom.TensorSumEigenvalues
