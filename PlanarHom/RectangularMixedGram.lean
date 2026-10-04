import PlanarHom.RectangularDoubleDiamondSemantics

/-! NEW physical mixed Gram forms obtained from literal finite sums. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularMixedGadgets
variable {X Y R : Type} [CommSemiring R]

private theorem entrySquare_fromBlocks {A B C D : Type}
    (M : Matrix A C R) (N : Matrix A D R) (P : Matrix B C R) (Q : Matrix B D R) :
    entrySquare (Matrix.fromBlocks M N P Q) =
      Matrix.fromBlocks (entrySquare M) (entrySquare N) (entrySquare P) (entrySquare Q) := by
  ext i j
  cases i <;> cases j <;> rfl

private theorem entrySquare_zero {A B : Type} : entrySquare (0 : Matrix A B R)=0 := by
  ext i j
  simp [entrySquare]

variable [Fintype X] [Fintype Y]

/-- The eight actual edges give the parallel-square Gram for symmetric K.
The identity remains valid for empty sides and arbitrary coefficient signs. -/
theorem doubleDiamond_physical_gram (B : Matrix X Y R) (K : Matrix X X R)
    (hK : K.transpose=K) :
    TwoTerminal.coloredSignature doubleDiamond
      (edgeMatrices (onX K) (cross B)) (fun _=>1) =
      onX (entrySquare (K*B)*(entrySquare (K*B)).transpose) := by
  rw [doubleDiamond_value]
  have h₁ : onX (Y:=Y) K * cross B = Matrix.fromBlocks 0 (K*B) 0 0 := by
    simp [onX,cross,Matrix.fromBlocks_multiply]
  have h₂ : cross B * onX (Y:=Y) K = Matrix.fromBlocks 0 0 (B.transpose*K) 0 := by
    simp [onX,cross,Matrix.fromBlocks_multiply]
  have h₃ : B.transpose*K=(K*B).transpose := by
    rw [Matrix.transpose_mul,hK]
  rw [h₁,h₂,h₃,entrySquare_fromBlocks,entrySquare_fromBlocks]
  simp only [entrySquare_zero,Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,
    add_zero,zero_add]
  rfl

end PlanarHom.RectangularMixedGadgets
