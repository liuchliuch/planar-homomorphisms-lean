import PlanarHom.TypedBipartiteSpectralPaths
import Mathlib.Data.Matrix.Block

/-! Only the selected X block participates in interpolation. Extending its
projectors by zero avoids every extra product relation from dummy eigenvalues. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.TypedBipartiteSpectral
variable {X Y R : Type} [CommSemiring R]

/-- Same-side matrices are zero away from their actual X×X domain. -/
def zeroExtend (A : Matrix X X R) : Matrix (X ⊕ Y) (X ⊕ Y) R :=
  Matrix.fromBlocks A 0 0 0

@[simp] theorem zeroExtend_inl (A : Matrix X X R) (x y : X) :
    zeroExtend (Y:=Y) A (.inl x) (.inl y)=A x y := rfl

@[simp] theorem zeroExtend_inr_left (A : Matrix X X R) (x : Y) (y : X ⊕ Y) :
    zeroExtend A (.inr x) y=0 := by cases y <;> rfl

@[simp] theorem zeroExtend_inr_right (A : Matrix X X R) (x : X ⊕ Y) (y : Y) :
    zeroExtend A x (.inr y)=0 := by cases x <;> rfl

/-- Linearity retains exactly the original X-supported spectral index set. -/
theorem zeroExtend_sum_smul {t : ℕ} (P : Fin t → Matrix X X R) (a : Fin t → R) :
    zeroExtend (Y:=Y) (∑ i,a i • P i)=∑ i,a i • zeroExtend (Y:=Y) (P i) := by
  ext (x|x) (y|y) <;> simp [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Only positive sample powers are used. Exponent zero deliberately does not
assert that the X identity is the ambient identity. -/
theorem zeroExtend_pow (A : Matrix X X R) (n : ℕ) (hn : 0<n) :
    zeroExtend (Y:=Y) A ^ n=zeroExtend (Y:=Y) (A^n) := by
  simp only [zeroExtend,Matrix.fromBlocks_diagonal_pow,zero_pow (Nat.ne_of_gt hn)]

/-- A completion on Y does not change a full-color path sum with X endpoints.
The second sum is the path with every private vertex genuinely restricted to X.
This includes selected loops and permits a rectangular ambient X⊕Y. -/
theorem completed_path_sum_eq_private_X (A : Matrix X X R) (E : Matrix Y Y R)
    (n : ℕ) (x y : X) :
    (∑ τ : Fin n → X ⊕ Y,
      PathPower.weight n (Matrix.fromBlocks A 0 0 E) (.inl x) (.inl y) τ)=
    ∑ τ : Fin n → X,PathPower.weight n A x y τ := by
  rw [PathPower.sum_weight,PathPower.sum_weight,Matrix.fromBlocks_diagonal_pow]
  rfl

/-- The X identity stays supported on X even at rational exponent zero. -/
@[simp] theorem zeroExtend_one_inr (y : Y) :
    zeroExtend (1 : Matrix X X R) (.inr y) (.inr y)=0 := rfl

end PlanarHom.TypedBipartiteSpectral
