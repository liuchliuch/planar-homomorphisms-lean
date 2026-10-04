import PlanarHom.RectangularSubsetCoefficients

/-! NEW exact two-row convolution and the degree-two physical coefficient. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean Polynomial
variable {d:ℕ}

def xorEquiv (S:Cube d):Cube d≃Cube d where
  toFun:=fun T=>xor S T
  invFun:=fun T=>xor S T
  left_inv:=by intro T;funext i;simp [Boolean.xor]
  right_inv:=by intro T;funext i;simp [Boolean.xor]

def rowConvolution (u v:Cube d→ℝ) (T:Cube d):ℝ:=∑J:Cube d,u J*v (xor T J)

theorem rowConvolution_comm (u v:Cube d→ℝ) (T:Cube d):rowConvolution u v T=rowConvolution v u T:=by
  unfold rowConvolution
  apply Fintype.sum_equiv (xorEquiv T)
  intro J
  change u J*v (xor T J)=v (xor T J)*u (xor T (xor T J))
  have he:xor T (xor T J)=J:=by funext i;simp [Boolean.xor]
  rw [he,mul_comm]

theorem split_empty (C:Matrix (Cube d) (Cube d) ℝ)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0) (S T:Cube d):
    splitConvolution C S T (fun _=>false)=C S T:=by
  simp [splitConvolution,hrow,ite_mul]

theorem split_self (C:Matrix (Cube d) (Cube d) ℝ)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0) (S T:Cube d):
    splitConvolution C S T S=C S T:=by
  simp [splitConvolution,hrow,xor_eq_zero_iff,mul_ite]

theorem squareCoefficient_pair (C:Matrix (Cube d) (Cube d) ℝ)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0)
    (i k:Fin d) (hik:i≠k) (T:Cube d):
    (squareCoefficientPolynomial C (pairBits i k) T).coeff 2=
      2*(C (pairBits i k) T+rowConvolution (C (unitBit i)) (C (unitBit k)) T):=by
  rw [squareCoefficient_pair_decomposition C i k hik T,split_empty C hrow,split_self C hrow]
  have hi:splitConvolution C (pairBits i k) T (unitBit i)=
      rowConvolution (C (unitBit i)) (C (unitBit k)) T:=by
    simp only [splitConvolution,pairBits_xor_left i k hik,rowConvolution]
  have hk:splitConvolution C (pairBits i k) T (unitBit k)=
      rowConvolution (C (unitBit k)) (C (unitBit i)) T:=by
    simp only [splitConvolution,pairBits_xor_right i k hik,rowConvolution]
  rw [hi,hk,rowConvolution_comm (C (unitBit k))]
  ring

end PlanarHom.RectangularWalshConvolution
