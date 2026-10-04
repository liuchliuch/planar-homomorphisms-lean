import PlanarHom.FinitePermutationCycleInsertion
import PlanarHom.FinitePermutationCycleTransport
import Mathlib.GroupTheory.Perm.List

/-! NEW exact erasure/insertion algebra for fixed tree-dart markers in a contour.
Only paired visible darts affect the face-cycle count. -/
noncomputable section
namespace PlanarHom.FinitePermutationCycles
variable {A : Type*} [DecidableEq A]

/-- Inserting a fixed marker after a contour dart inserts it after the reverse
predecessor in the face permutation. -/
theorem insertAfter_mul_fixed (C I : Equiv.Perm A) (a : A) :
    insertAfter C a * Equiv.sumCongr I (Equiv.refl Unit)=
      insertAfter (C*I) (I.symm a) := by
  ext x
  cases x with
  | inl x =>
      change insertAfter C a (.inl (I x))=insertAfter (C*I) (I.symm a) (.inl x)
      by_cases hx : x=I.symm a
      · subst x
        rw [I.apply_symm_apply,insertAfter_mark,insertAfter_mark]
      · have hix : I x≠a := by
          intro h
          exact hx (I.injective (h.trans (I.apply_symm_apply a).symm))
        rw [insertAfter_old C a _ hix,insertAfter_old (C*I) _ x hx]
        rfl
  | inr u =>
      cases u
      change insertAfter C a (.inr ())=insertAfter (C*I) (I.symm a) (.inr ())
      rw [insertAfter_new,insertAfter_new]
      simp only [Equiv.Perm.mul_apply,I.apply_symm_apply]

theorem count_insert_fixed_marker [Finite A] (C I : Equiv.Perm A) (a : A) :
    count (insertAfter C a * Equiv.sumCongr I (Equiv.refl Unit))=count (C*I) := by
  rw [insertAfter_mul_fixed,count_insertAfter]

private theorem map_formPerm_apply {B : Type*} [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (hn : xs.Nodup) {a : A} (ha : a∈xs) :
    (xs.map f).formPerm (f a)=f (xs.formPerm a) := by
  obtain ⟨i,hi,hget⟩ := List.mem_iff_getElem.mp ha
  rw [←hget]
  have hm := List.formPerm_apply_getElem (xs.map f) (hn.map hf) i (by simpa using hi)
  simpa only [List.getElem_map,List.length_map,List.formPerm_apply_getElem xs hn i hi] using hm

/-- A new first entry in a complete cyclic row is exactly one cycle insertion. -/
theorem formPerm_new_cons (head : A) (tail : List A) (hn : (head::tail).Nodup)
    (hfull : ∀ a, a∈head::tail) :
    (Sum.inr () :: (head::tail).map Sum.inl).formPerm=
      insertAfter (head::tail).formPerm ((head::tail).getLast (by simp)) := by
  ext x
  cases x with
  | inl x =>
      have hx := hfull x
      have hm := map_formPerm_apply (Sum.inl (β:=Unit)) Sum.inl_injective
        (head::tail) hn hx
      have hnot : Sum.inr ()∉(head::tail).map (Sum.inl (β:=Unit)) := by simp
      change (Sum.inr ()::Sum.inl head::tail.map Sum.inl).formPerm (.inl x)=_
      rw [List.formPerm_cons_cons,Equiv.Perm.mul_apply]
      change Equiv.swap (.inr ()) (.inl head) (((head::tail).map Sum.inl).formPerm (.inl x))=_
      rw [hm]
      by_cases hxlast : x=(head::tail).getLast (by simp)
      · rw [hxlast,List.formPerm_apply_getLast,Equiv.swap_apply_right,insertAfter_mark]
      · have hnext : (head::tail).formPerm x≠head := by
          intro h
          exact hxlast ((List.formPerm_eq_head_iff_eq_getLast tail x head).mp h)
        rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa only [ne_eq,Sum.inl.injEq] using hnext),
          insertAfter_old _ _ x hxlast]
  | inr u =>
      cases u
      rw [insertAfter_new,List.formPerm_apply_getLast]
      change (Sum.inr ()::Sum.inl head::tail.map Sum.inl).formPerm (.inr ())=.inl head
      apply List.formPerm_apply_head
      have hm : ((head::tail).map (Sum.inl (β:=Unit))).Nodup := hn.map Sum.inl_injective
      exact List.nodup_cons.mpr ⟨by simp,hm⟩

end PlanarHom.FinitePermutationCycles
