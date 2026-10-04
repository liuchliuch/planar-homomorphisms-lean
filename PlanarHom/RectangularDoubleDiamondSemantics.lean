import PlanarHom.RectangularDoubleDiamondGraph
import PlanarHom.RectangularMixedBlockCoordinates

/-! NEW exact finite-sum evaluation of the actual eight edge occurrences. -/
noncomputable section
set_option maxHeartbeats 800000
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularMixedGadgets
local instance (priority := 10000) (α : Type) : DecidableEq α := Classical.decEq α
variable {C R : Type} [Fintype C] [CommSemiring R]

private def fiveEquiv : (Fin 5 → C) ≃ C × C × C × C × C where
  toFun f := (f 2,f 4,f 3,f 1,f 0)
  invFun p := ![p.2.2.2.2,p.2.2.2.1,p.1,p.2.2.1,p.2.1]
  left_inv f := by funext k; fin_cases k <;> rfl
  right_inv p := by rcases p with ⟨a,b,c,d,e⟩; rfl

private theorem sum_five (f : (Fin 5 → C) → R) :
    (∑ η, f η) = ∑ c, ∑ e, ∑ d, ∑ b, ∑ a, f ![a,b,c,d,e] := by
  calc
    _ = ∑ p : C × C × C × C × C, f (fiveEquiv.symm p) := by
      apply Fintype.sum_equiv fiveEquiv
      intro η
      rw [Equiv.symm_apply_apply]
    _ = _ := by simp only [Fintype.sum_prod_type]; rfl

omit [Fintype C] in
private theorem product_edges (K B : Matrix C C R) (i j : C) (η : Fin 5→C) :
    (∏ e,edgeMatrices K B e (TwoTerminal.extend i j η (doubleDiamond.src e))
      (TwoTerminal.extend i j η (doubleDiamond.dst e))) =
      K i (η 0)*B (η 0) (η 2)*K i (η 1)*B (η 1) (η 2)*
        B (η 2) (η 3)*K (η 3) j*B (η 2) (η 4)*K (η 4) j := by
  simp only [Fin.prod_univ_eight]
  rfl

/-- Independent branch sums square entrywise on either side of the shared color. -/
theorem doubleDiamond_value (K B : Matrix C C R) :
    TwoTerminal.coloredSignature doubleDiamond (edgeMatrices K B) (fun _=>1) =
      entrySquare (K*B) * entrySquare (B*K) := by
  funext i j
  simp only [TwoTerminal.coloredSignature,Finset.prod_const_one,one_mul,product_edges]
  calc
    _ = ∑ c, ∑ e, ∑ d, ∑ b, ∑ a,
        K i a*B a c*K i b*B b c*B c d*K d j*B c e*K e j :=
      sum_five (fun η=>K i (η 0)*B (η 0) (η 2)*K i (η 1)*B (η 1) (η 2)*
        B (η 2) (η 3)*K (η 3) j*B (η 2) (η 4)*K (η 4) j)
    _ = _ := by
      simp only [entrySquare,Matrix.mul_apply,pow_two,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      ring

end PlanarHom.RectangularMixedGadgets
