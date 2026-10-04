import PlanarHom.PlanarityLRContourEventOrder

/-! NEW literal two-element sublist and flat-map order transport helpers. -/
namespace PlanarHom.ListPairSublistOrder

 theorem flatMap_sublist {A B : Type} (f : A→List B) {xs ys : List A} (h : xs.Sublist ys) :
    (xs.flatMap f).Sublist (ys.flatMap f) := by
  induction h with
  | slnil => simp
  | @cons xs ys a h ih => exact ih.trans (List.sublist_append_right (f a) (ys.flatMap f))
  | @cons₂ xs ys a h ih => exact ih.append_left (f a)

 theorem member_flatMap_sublist {A B : Type} (f : A→List B) {a : A} {xs : List A} (ha : a∈xs) :
    (f a).Sublist (xs.flatMap f) := by
  simpa using flatMap_sublist f (List.singleton_sublist.mpr ha)

 theorem pair_of_idxOf_lt (xs : List ℕ) {a b : ℕ} (ha : a∈xs) (hb : b∈xs)
    (hab : xs.idxOf a<xs.idxOf b) : [a,b].Sublist xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    by_cases hxa:x=a
    · subst x
      have hba:b≠a := by intro h; subst b; omega
      have hbt:b∈xs:=by simpa [hba] using hb
      exact (List.singleton_sublist.mpr hbt).cons₂ a
    · have hat:a∈xs:=by simpa [Ne.symm hxa] using ha
      by_cases hxb:x=b
      · subst x
        simp only [List.idxOf_cons_self] at hab
        omega
      · have hbt:b∈xs:=by simpa [Ne.symm hxb] using hb
        have hab':xs.idxOf a<xs.idxOf b := by
          simpa [List.idxOf_cons,Bool.beq_eq_decide_eq,hxa,hxb] using hab
        exact (ih hat hbt hab').cons x

 theorem pair_across_append {A : Type} {a b : A} {xs ys : List A} (ha : a∈xs) (hb : b∈ys) :
    [a,b].Sublist (xs++ys) :=
   (List.singleton_sublist.mpr ha).append (List.singleton_sublist.mpr hb)

end PlanarHom.ListPairSublistOrder
