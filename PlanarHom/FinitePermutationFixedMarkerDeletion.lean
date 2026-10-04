import PlanarHom.FinitePermutationFixedMarker
import Mathlib.Data.Sum.Basic

/-! NEW exact deletion of one fixed marker from a complete cyclic row. -/
noncomputable section
namespace PlanarHom.FinitePermutationCycles
variable {A : Type*} [DecidableEq A]

def eraseRight (xs : List (A ⊕ Unit)) : List A := xs.filterMap Sum.getLeft?

 theorem map_eraseRight (xs : List (A ⊕ Unit)) (hn : Sum.inr ()∉xs) :
    (eraseRight xs).map Sum.inl=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have ht : Sum.inr ()∉xs := fun h => hn (List.mem_cons_of_mem _ h)
      cases x with
      | inl a => simp only [eraseRight,List.filterMap_cons,Sum.getLeft?_inl,List.map_cons]; exact congrArg _ (ih ht)
      | inr u => cases u; exact (hn (List.mem_cons_self ..)).elim

 theorem count_delete_fixed_marker [Finite A] [Nonempty A] (I : Equiv.Perm A)
    (xs : List (A ⊕ Unit)) (hn : xs.Nodup) (hfull : ∀x,x∈xs) :
    count (xs.formPerm * Equiv.sumCongr I (Equiv.refl Unit))=
      count ((eraseRight xs).formPerm * I) := by
  obtain ⟨pre,post,rfl⟩ := List.append_of_mem (hfull (.inr ()))
  let ys := post++pre
  let old := eraseRight ys
  have hrot : (pre++Sum.inr ()::post).rotate pre.length=Sum.inr ()::ys := by
    simpa only [ys,List.cons_append] using List.rotate_append_length_eq pre (Sum.inr ()::post)
  have hnd : (Sum.inr ()::ys).Nodup := hrot ▸ List.nodup_rotate.mpr hn
  have hmap : old.map Sum.inl=ys := map_eraseRight ys (List.nodup_cons.mp hnd).1
  have hnOld : old.Nodup := List.Nodup.of_map Sum.inl (hmap ▸ (List.nodup_cons.mp hnd).2)
  have hfullOld : ∀a,a∈old := by
    intro a
    have hm : Sum.inl a∈Sum.inr ()::ys := by
      rw [←hrot,List.mem_rotate]
      exact hfull (.inl a)
    have hmy : Sum.inl a∈ys := (List.mem_cons.mp hm).resolve_left (by simp)
    rw [←hmap] at hmy
    obtain ⟨b,hb,hba⟩ := List.mem_map.mp hmy
    exact Sum.inl.inj hba ▸ hb
  have hproj : eraseRight (pre++Sum.inr ()::post)=eraseRight pre++eraseRight post := by
    simp only [eraseRight,List.filterMap_append,List.filterMap_cons,Sum.getLeft?_inr]
  have hperm : old.Perm (eraseRight (pre++Sum.inr ()::post)) := by
    rw [hproj]
    change (eraseRight (post++pre)).Perm _
    simp only [eraseRight,List.filterMap_append]
    exact List.perm_append_comm
  have hnProj := hperm.nodup_iff.mp hnOld
  have hrotOld : (eraseRight (pre++Sum.inr ()::post)).rotate (eraseRight pre).length=old := by
    rw [hproj,List.rotate_append_length_eq]
    simp only [old,ys,eraseRight,List.filterMap_append]
  have hforms : old.formPerm=(eraseRight (pre++Sum.inr ()::post)).formPerm := by
    rw [←hrotOld]
    exact List.formPerm_rotate _ hnProj _
  have hC : (pre++Sum.inr ()::post).formPerm=(Sum.inr ()::old.map Sum.inl).formPerm := by
    rw [hmap,←hrot]
    exact (List.formPerm_rotate _ hn _).symm
  rw [hC]
  cases hold : old with
  | nil =>
      obtain ⟨a⟩ := ‹Nonempty A›
      have ha := hfullOld a
      simp only [hold,List.not_mem_nil] at ha
  | cons a tail =>
      have hno : (a::tail).Nodup := hold ▸ hnOld
      have hfo : ∀b,b∈a::tail := fun b => hold ▸ hfullOld b
      rw [formPerm_new_cons a tail hno hfo,count_insert_fixed_marker]
      rw [←hold,hforms]

end PlanarHom.FinitePermutationCycles
