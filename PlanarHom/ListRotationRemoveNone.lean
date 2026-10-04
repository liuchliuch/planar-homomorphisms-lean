import PlanarHom.PlanarityLRRealizationRotationSystem
import PlanarHom.FinitePermutationMarkerErasure

/-! Removing an actual marker from an arbitrary cyclic row agrees exactly
with filtering the marker out of its linear presentation. Empty/singleton rows
are included, and no connectedness of the full rotation is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.ListRotationErasure
open Equiv
variable {A : Type} [DecidableEq A]

theorem mem_filterSome (xs : List (Option A)) (a : A) :
    a∈xs.filterMap id ↔ some a∈xs := by simp [List.mem_filterMap]

theorem filterSome_nodup (xs : List (Option A)) (h : xs.Nodup) : (xs.filterMap id).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases a with
    | none => exact ih h.of_cons
    | some a =>
      simp only [List.filterMap_cons,id_eq,List.nodup_cons]
      exact ⟨fun hm=>h.not_mem (mem_filterSome xs a |>.mp hm),ih h.of_cons⟩

theorem map_some_filterSome (xs : List (Option A)) (h : none∉xs) :
    (xs.filterMap id).map some=xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases a with
    | none => exact False.elim (h (by simp))
    | some a =>
      simp only [List.filterMap_cons,id_eq,List.map_cons]
      rw [ih (fun hh=>h (List.mem_cons_of_mem _ hh))]

theorem formPerm_map_some (xs : List A) (h : xs.Nodup) :
    (xs.map some).formPerm=xs.formPerm.optionCongr := by
  apply Equiv.ext
  intro x
  cases x with
  | none =>
    rw [List.formPerm_apply_of_notMem (by simp)]
    rfl
  | some a =>
    by_cases ha : a∈xs
    · exact PlanarityLRRealization.map_formPerm_apply some (Option.some_injective _) xs h ha
    · rw [List.formPerm_apply_of_notMem (by simpa using ha)]
      simp only [Equiv.optionCongr_apply,Option.map_some,List.formPerm_apply_of_notMem ha]

theorem removeNone_none_cons (xs : List A) (h : xs.Nodup) :
    Equiv.removeNone (none::xs.map some).formPerm=xs.formPerm := by
  cases xs with
  | nil =>
    change Equiv.removeNone (Equiv.refl (Option A))=Equiv.refl A
    exact Equiv.removeNone_optionCongr (Equiv.refl A)
  | cons a xs =>
    have he : (some a::xs.map some).formPerm=(a::xs).formPerm.optionCongr := formPerm_map_some _ h
    simp only [List.map_cons,List.formPerm_cons_cons]
    rw [he]
    apply Equiv.optionCongr_injective
    rw [map_equiv_removeNone]
    have hn : (Equiv.swap none (some a)*(a::xs).formPerm.optionCongr) none=some a := by simp
    rw [hn,←mul_assoc,Equiv.swap_mul_self,one_mul]

/-- Single-row deletion is literally list filtering, independently of where
the row was cyclically cut before deletion. -/
theorem removeNone_formPerm (xs : List (Option A)) (h : xs.Nodup) :
    Equiv.removeNone xs.formPerm=(xs.filterMap id).formPerm := by
  by_cases hn : none∈xs
  · obtain ⟨l,r,rfl⟩:=List.mem_iff_append.mp hn
    have hr : (l++none::r).formPerm=(none::(r++l)).formPerm :=
      List.formPerm_eq_of_isRotated h List.isRotated_append
    have hnr : (none::(r++l)).Nodup := (List.isRotated_append : (l++none::r) ~r ((none::r)++l)).nodup_iff.mp h
    have hm := map_some_filterSome (r++l) hnr.not_mem
    rw [hr,←hm,removeNone_none_cons _ (filterSome_nodup _ hnr.of_cons)]
    have hh := filterSome_nodup (l++none::r) h
    simp only [List.filterMap_append,List.filterMap_cons,id_eq] at hh ⊢
    exact (List.formPerm_eq_of_isRotated hh List.isRotated_append).symm
  · have hm := map_some_filterSome xs hn
    rw [←hm,formPerm_map_some _ (filterSome_nodup xs h),Equiv.removeNone_optionCongr]
    simp only [List.filterMap_map,Function.comp_def,id_eq,List.filterMap_some]

end PlanarHom.ListRotationErasure
