import PlanarHom.FinitePermutationFixedMarkerDeletion
import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Equiv.Sum

/-! NEW erasure of every fixed contour marker, retaining exact paired cyclic
order and literal face-cycle count whenever at least one visible dart exists. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
universe u v w
variable {A : Type u} {B : Type v}

theorem formPerm_eq_classical [d : DecidableEq A] (xs : List A) :
    xs.formPerm=@List.formPerm A (Classical.decEq A) xs := by
  have h : d=Classical.decEq A := Subsingleton.elim _ _
  cases h
  rfl

private theorem map_formPerm_full [DecidableEq A] [DecidableEq B]
    (e : A≃B) (xs : List A) (hn : xs.Nodup) (hfull : ∀a,a∈xs) (a : A) :
    (xs.map e).formPerm (e a)=e (xs.formPerm a) := by
  obtain ⟨i,hi,hget⟩ := List.mem_iff_getElem.mp (hfull a)
  rw [←hget]
  have hm := List.formPerm_apply_getElem (xs.map e) (hn.map e.injective) i (by simpa using hi)
  simpa only [List.getElem_map,List.length_map,List.formPerm_apply_getElem xs hn i hi] using hm

 theorem count_mapped_word [Finite A] [Finite B] [DecidableEq A] [DecidableEq B]
    (I : Equiv.Perm A) (J : Equiv.Perm B) (e : A≃B) (he : ∀a,e (I a)=J (e a))
    (xs : List A) (hn : xs.Nodup) (hfull : ∀a,a∈xs) :
    count ((xs.map e).formPerm*J)=count (xs.formPerm*I) := by
  symm
  apply count_of_step _ _ e
  intro a
  change e (xs.formPerm (I a))=(xs.map e).formPerm (J (e a))
  rw [←he,map_formPerm_full e xs hn hfull]

 def visibleWord {M : Type*} (xs : List (A ⊕ M)) : List A := xs.filterMap Sum.getLeft?

 theorem visibleWord_map_left {M : Type*} (xs : List (A ⊕ M)) :
    (visibleWord xs).map Sum.inl=xs.filter Sum.isLeft := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all [visibleWord]

 theorem visibleWord_nodup {M : Type*} {xs : List (A ⊕ M)} (hn : xs.Nodup) :
    (visibleWord xs).Nodup := by
  apply List.Nodup.of_map (Sum.inl (β:=M))
  rw [visibleWord_map_left]
  exact hn.filter _

 theorem visibleWord_full {M : Type*} {xs : List (A ⊕ M)} (hfull : ∀x,x∈xs) :
    ∀a,a∈visibleWord xs := by
  intro a
  exact List.mem_filterMap.mpr ⟨.inl a,hfull _,rfl⟩

 theorem visibleWord_map_markerEquiv {M N : Type*} (e : M≃N) (xs : List (A ⊕ M)) :
    visibleWord (xs.map (Equiv.sumCongr (Equiv.refl A) e))=visibleWord xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all [visibleWord]

 def optionMarkerEquiv (A M : Type*) : ((A ⊕ M) ⊕ Unit) ≃ A ⊕ Option M where
  toFun
    | .inl (.inl a) => .inl a
    | .inl (.inr m) => .inr (some m)
    | .inr _ => .inr none
  invFun
    | .inl a => .inl (.inl a)
    | .inr (some m) => .inl (.inr m)
    | .inr none => .inr ()
  left_inv x := by
    rcases x with (a | m) | u
    · rfl
    · rfl
    · cases u; rfl
  right_inv x := by rcases x with a | (_ | m) <;> rfl

 theorem visibleWord_optionMarker (M : Type*) (xs : List (A ⊕ Option M)) :
    visibleWord (eraseRight (xs.map (optionMarkerEquiv A M).symm))=visibleWord xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rcases x with a | (_ | m) <;> simp_all [visibleWord,eraseRight,optionMarkerEquiv]

 theorem count_erase_fixed_markers [Finite A] [Nonempty A] [DecidableEq A]
    (M : Type w) [Finite M] (I : Equiv.Perm A)
    (xs : List (A ⊕ M)) (hn : xs.Nodup) (hfull : ∀x,x∈xs) :
    count (xs.formPerm * Equiv.sumCongr I (Equiv.refl M))=
      count ((visibleWord xs).formPerm * I) := by
  letI := Fintype.ofFinite M
  suffices h : ∀ (M : Type w) [Fintype M], ∀ (xs : List (A ⊕ M)), xs.Nodup → (∀x,x∈xs) →
      count (xs.formPerm * Equiv.sumCongr I (Equiv.refl M))=count ((visibleWord xs).formPerm * I) by
    exact h M xs hn hfull
  intro M hM
  letI : Fintype M := hM
  refine Fintype.induction_empty_option
    (P := fun M _ => ∀ (xs : List (A ⊕ M)), xs.Nodup → (∀x,x∈xs) →
    count (xs.formPerm * Equiv.sumCongr I (Equiv.refl M))=count ((visibleWord xs).formPerm * I))
    ?_ ?_ ?_ M
  · intro M N hN e ih
    letI : Fintype N := hN
    letI : Fintype M := Fintype.ofEquiv N e.symm
    intro xs hn hfull
    let E := Equiv.sumCongr (Equiv.refl A) e
    let ys := xs.map E.symm
    have hyn : ys.Nodup := hn.map E.symm.injective
    have hyf : ∀y,y∈ys := by
      intro y
      exact List.mem_map.mpr ⟨E y,hfull _,E.symm_apply_apply y⟩
    have ht := count_mapped_word (Equiv.sumCongr I (Equiv.refl M))
      (Equiv.sumCongr I (Equiv.refl N)) E (by intro x; cases x <;> rfl) ys hyn hyf
    have hmap : ys.map E=xs := by simp [ys,List.map_map]
    rw [hmap] at ht
    simp only [formPerm_eq_classical] at ht ⊢
    rw [ht]
    have hi := ih ys hyn hyf
    simp only [formPerm_eq_classical] at hi
    rw [hi]
    have hw : visibleWord ys=visibleWord xs := visibleWord_map_markerEquiv e.symm xs
    rw [hw]
  ·
    intro xs hn hfull
    let E := Equiv.sumEmpty A PEmpty
    have ht := count_mapped_word (Equiv.sumCongr I (Equiv.refl PEmpty)) I E
      (by intro x; rcases x with a | m; rfl; exact m.elim) xs hn hfull
    have hw : xs.map E=visibleWord xs := by
      clear hn hfull ht
      induction xs with
      | nil => rfl
      | cons x xs ih =>
          rcases x with a | m
          · simpa only [List.map_cons,visibleWord,List.filterMap_cons,Sum.getLeft?_inl] using congrArg (List.cons a) ih
          · exact m.elim
    rw [hw] at ht
    simpa only [formPerm_eq_classical] using ht.symm
  · intro M hM ih
    letI : Fintype M := hM
    intro xs hn hfull
    let E := optionMarkerEquiv A M
    let ys := xs.map E.symm
    have hyn : ys.Nodup := hn.map E.symm.injective
    have hyf : ∀y,y∈ys := by
      intro y
      exact List.mem_map.mpr ⟨E y,hfull _,E.symm_apply_apply y⟩
    have ht := count_mapped_word
      (Equiv.sumCongr (Equiv.sumCongr I (Equiv.refl M)) (Equiv.refl Unit))
      (Equiv.sumCongr I (Equiv.refl (Option M))) E
      (by intro x; rcases x with (a | m) | u <;> rfl) ys hyn hyf
    have hmap : ys.map E=xs := by simp [ys,List.map_map]
    rw [hmap] at ht
    simp only [formPerm_eq_classical] at ht ⊢
    rw [ht]
    have hd := count_delete_fixed_marker (Equiv.sumCongr I (Equiv.refl M)) ys hyn hyf
    simp only [formPerm_eq_classical] at hd
    rw [hd]
    have hon : (eraseRight ys).Nodup := visibleWord_nodup hyn
    have hof : ∀a,a∈eraseRight ys := visibleWord_full hyf
    have hi := ih _ hon hof
    simp only [formPerm_eq_classical] at hi
    rw [hi]
    have hw : visibleWord (eraseRight ys)=visibleWord xs := visibleWord_optionMarker M xs
    rw [hw]
end PlanarHom.FinitePermutationCycles
