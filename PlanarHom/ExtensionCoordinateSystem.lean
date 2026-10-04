import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Pi

/-! NEW: a dynamic matrix over a fixed finite field extension is exactly the
coordinate block system over the base field. This is pure algebra; concrete
coordinate materialization and its runtime are separate theorems. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.ExtensionCoordinateSystem
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n e : ℕ}
variable (basis : Module.Basis (Fin e) K L)

def coordinates : (Fin n → L) ≃ₗ[K] (Fin n × Fin e → K) where
  toFun x p := basis.equivFun (x p.1) p.2
  invFun y i := basis.equivFun.symm (fun k => y (i,k))
  left_inv x := by funext i; exact basis.equivFun.symm_apply_apply (x i)
  right_inv y := by
    funext p
    exact congrFun (basis.equivFun.apply_symm_apply (fun k => y (p.1,k))) p.2
  map_add' x y := by ext p; simp
  map_smul' a x := by ext p; simp

def block (A : Matrix (Fin n) (Fin n) L) :
    Matrix (Fin n × Fin e) (Fin n × Fin e) K :=
  fun p q => basis.repr (A p.1 q.1 * basis q.2) p.2

theorem multiplication_coordinates (a x : L) (k : Fin e) :
    basis.repr (a*x) k = ∑ l, basis.repr (a*basis l) k * basis.repr x l := by
  change basis.equivFun (a*x) k = ∑ l, basis.equivFun (a*basis l) k * basis.equivFun x l
  conv_lhs => rw [← basis.sum_equivFun x]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Exact block multiplication, with row-major pairs `(i,k)` and `(j,l)`. -/
theorem block_mulVec (A : Matrix (Fin n) (Fin n) L) (x : Fin n → L) :
    (block basis A).mulVec (coordinates basis x) = coordinates basis (A.mulVec x) := by
  funext p
  simp only [Matrix.mulVec, dotProduct, block, coordinates, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type]
  change (∑ j, ∑ l, basis.repr (A p.1 j * basis l) p.2 * basis.repr (x j) l) =
    basis.repr (∑ j, A p.1 j * x j) p.2
  change (∑ j, ∑ l, basis.equivFun (A p.1 j * basis l) p.2 * basis.equivFun (x j) l) =
    basis.equivFun (∑ j, A p.1 j * x j) p.2
  simp only [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact (multiplication_coordinates basis (A p.1 j) (x j) p.2).symm

theorem solution_iff (A : Matrix (Fin n) (Fin n) L) (b x : Fin n → L) :
    (block basis A).mulVec (coordinates basis x) = coordinates basis b ↔ A.mulVec x = b := by
  rw [block_mulVec, (coordinates basis).injective.eq_iff]

theorem decoded_solution_iff (A : Matrix (Fin n) (Fin n) L)
    (b : Fin n → L) (y : Fin n × Fin e → K) :
    (block basis A).mulVec y = coordinates basis b ↔
      A.mulVec ((coordinates basis).symm y) = b := by
  simpa using solution_iff basis A b ((coordinates basis).symm y)

theorem kernel_iff (A : Matrix (Fin n) (Fin n) L) (x : Fin n → L) :
    (block basis A).mulVec (coordinates basis x) = 0 ↔ A.mulVec x = 0 := by
  simpa using solution_iff basis A 0 x

theorem mulVec_injective_iff (A : Matrix (Fin n) (Fin n) L) :
    Function.Injective (block basis A).mulVec ↔ Function.Injective A.mulVec := by
  constructor
  · intro h x y hxy
    apply (coordinates basis).injective
    apply h
    simp only [block_mulVec, hxy]
  · intro h x y hxy
    apply (coordinates basis).symm.injective
    apply h
    apply (coordinates basis).injective
    simpa only [← block_mulVec, LinearEquiv.apply_symm_apply] using hxy

/-- Nonsingularity is preserved in both directions, without a nonempty
matrix-order assumption or a supplied inverse. -/
theorem det_ne_zero_iff (A : Matrix (Fin n) (Fin n) L) :
    (block basis A).det ≠ 0 ↔ A.det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.mulVec_injective_iff_isUnit, mulVec_injective_iff,
    Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]

end PlanarHom.ExtensionCoordinateSystem
