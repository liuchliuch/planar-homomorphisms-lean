import PlanarHom.FinitePermutationSwapBound
import Mathlib.GroupTheory.Perm.List

/-! Concatenating two exposed incidence blocks swaps exactly their closing
arrows. This identifies the actual row operation used by the source canvas. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open Equiv Equiv.Perm
variable {D : Type} [Fintype D]

 theorem formPerm_append_bridge (xs : List D) (a b : D) (ys : List D) :
    (xs++a::b::ys).formPerm=(xs++[a]).formPerm*Equiv.swap a b*(b::ys).formPerm := by
  induction xs with
  | nil => simp [List.formPerm_cons_cons]
  | cons x xs ih =>
    cases xs with
    | nil => simp [List.formPerm_cons_cons,mul_assoc]
    | cons y xs =>
      simpa only [List.cons_append,List.formPerm_cons_cons,mul_assoc] using
        congrArg (fun P : Equiv.Perm D => Equiv.swap x y*P) ih

 theorem formPerm_concat_closing (xs : List D) (a b : D) (ys : List D)
    (ha : a∉b::ys) :
    (xs++a::b::ys).formPerm=
      swapInput ((xs++[a]).formPerm*(b::ys).formPerm) a ((b::ys).getLast (by simp)) := by
  rw [formPerm_append_bridge]
  change _=((xs++[a]).formPerm*(b::ys).formPerm)*Equiv.swap a ((b::ys).getLast _)
  have hswap := Equiv.mul_swap_eq_swap_mul (b::ys).formPerm a ((b::ys).getLast (by simp))
  rw [List.formPerm_apply_of_notMem ha,List.formPerm_apply_getLast] at hswap
  rw [mul_assoc (xs++[a]).formPerm (b::ys).formPerm,hswap,mul_assoc]

 theorem face_of_row_swap (R J : Equiv.Perm D) (a b : D) :
    swapInput R a b*J=swapInput (R*J) (J.symm a) (J.symm b) := by
  change R*Equiv.swap a b*J=(R*J)*Equiv.swap (J.symm a) (J.symm b)
  have hswap := Equiv.mul_swap_eq_swap_mul J (J.symm a) (J.symm b)
  simp only [Equiv.apply_symm_apply] at hswap
  rw [mul_assoc R J,hswap,mul_assoc]
end PlanarHom.FinitePermutationCycles
