import PlanarHom.CountingCookLevinBlockLayers
import Mathlib.Data.List.FinRange

namespace PlanarHom.CountingCookLevin.Expr

/-- Fixed-size blocks can be emitted by independent arithmetic index formulas. -/
theorem regularLayer_ofFn {V : Type} {n : ℕ} (f : Fin n → Expr V) (C start : ℕ) (ρ : V → ℕ) :
    regularLayer (List.ofFn f) C start ρ=
      (List.finRange n).flatMap (fun i => (f i).regularBlock C (start+4*C*i.val) ρ) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ,regularLayer,List.finRange_succ,List.flatMap_cons,List.flatMap_map]
    simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero]
    congr 1
    rw [ih]
    apply List.flatMap_congr
    intro i _
    congr 1
    simp only [Fin.val_succ]
    ring

end PlanarHom.CountingCookLevin.Expr
