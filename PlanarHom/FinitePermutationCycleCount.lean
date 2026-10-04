import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! NEW literal finite permutation cycle count, including fixed points.
The empty carrier has zero cycles; no virtual outer face is included here. -/
noncomputable section
namespace PlanarHom.FinitePermutationCycles

variable {A B : Type*}

def count (P : Equiv.Perm A) : ℕ := Nat.card (Quotient (Equiv.Perm.SameCycle.setoid P))

theorem count_congr (P : Equiv.Perm A) (Q : Equiv.Perm B) (e : A≃B)
    (he : ∀a b,P.SameCycle a b ↔ Q.SameCycle (e a) (e b)) : count P=count Q := by
  exact Nat.card_congr (Quotient.congr e he)

@[simp] theorem count_empty [IsEmpty A] (P : Equiv.Perm A) : count P=0 := by
  simp [count]

@[simp] theorem count_one (A : Type*) : count (1 : Equiv.Perm A)=Nat.card A := by
  let e : Quotient (Equiv.Perm.SameCycle.setoid (1 : Equiv.Perm A))≃A :=
    { toFun := Quotient.lift (fun a=>a) (fun a b h=>Equiv.Perm.sameCycle_one.mp h)
      invFun := fun a=>Quotient.mk _ a
      left_inv := by intro a; refine Quotient.inductionOn a ?_; intro a; rfl
      right_inv := fun _=>rfl }
  exact Nat.card_congr e

end PlanarHom.FinitePermutationCycles
