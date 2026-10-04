import Mathlib.Data.Fin.Basic

/-! Join independently kernel-checked finite intervals without normalizing one
large nested universal decision tree. -/
namespace PlanarHom.FiniteIntervalCheck
 theorem append (P : ℕ → Prop) (a n m : ℕ)
    (hl : ∀i : Fin n,P (a+i.val)) (hr : ∀i : Fin m,P (a+n+i.val)) :
    ∀i : Fin (n+m),P (a+i.val) := by
  intro i
  refine Fin.addCases (fun j => hl j) (fun j => ?_) i
  change P (a+(n+j.val))
  simpa only [Nat.add_assoc] using hr j
end PlanarHom.FiniteIntervalCheck
