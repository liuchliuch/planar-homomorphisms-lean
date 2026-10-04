import Mathlib.LinearAlgebra.Matrix.PosDef

/-! NEW positive definiteness under an injective principal coordinate map.
The proof uses the actual coordinate-inclusion matrix and its injective linear
map, rather than assuming a submatrix is nonsingular. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom
variable {V I : Type} [Fintype V] [Fintype I]

theorem posDef_principal (A : Matrix V V ℝ) (hA : A.PosDef) (f : I → V)
    (hf : Function.Injective f) : (A.submatrix f f).PosDef := by
  let E : Matrix V I ℝ := (1 : Matrix V V ℝ).submatrix id f
  have hcoord (x : I → ℝ) (i : I) : E.mulVec x (f i)=x i := by
    simp [E,Matrix.mulVec,dotProduct,Matrix.one_apply,hf.eq_iff]
  have hi : Function.Injective E.mulVec := by
    intro x y h
    funext i
    exact (hcoord x i).symm.trans ((congrFun h (f i)).trans (hcoord y i))
  have he : E.conjTranspose*A*E=A.submatrix f f := by
    ext i j
    simp [E,Matrix.mul_apply,Matrix.submatrix_apply,Matrix.conjTranspose_apply,Matrix.one_apply]
  rw [←he]
  exact hA.conjTranspose_mul_mul_same hi

end PlanarHom
