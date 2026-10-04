import PlanarHom.PlanarityLRCyclicBlockInputs
import Mathlib.Data.List.Flatten

/-! NEW finite block-order facts used by the LR fork necessity argument. -/
namespace PlanarHom.PlanarityLRRealization

theorem pair_sublist_or_reverse {A : Type*} (xs : List A) {a b : A}
    (ha : a∈xs) (hb : b∈xs) (hne : a≠b) : [a,b].Sublist xs ∨ [b,a].Sublist xs := by
  induction xs with
  | nil => simp at ha
  | cons c xs ih =>
      rcases List.mem_cons.mp ha with hac | hat
      · have hb' : b∈xs := (List.mem_cons.mp hb).resolve_left (fun hbc => hne (hac.trans hbc.symm))
        exact Or.inl (by rw [hac]; exact (List.singleton_sublist.mpr hb').cons_cons c)
      · rcases List.mem_cons.mp hb with hbc | hbt
        · exact Or.inr (by rw [hbc]; exact (List.singleton_sublist.mpr hat).cons_cons c)
        · rcases ih hat hbt with h | h
          · exact Or.inl (h.cons c)
          · exact Or.inr (h.cons c)

theorem pair_sublist_flatMap {A B : Type*} (xs : List A) (block : A → List B)
    {a b : A} (h : [a,b].Sublist xs) {x y : B} (hx : x∈block a) (hy : y∈block b) :
    [x,y].Sublist (xs.flatMap block) := by
  have hxy := (List.singleton_sublist.mpr hx).append (List.singleton_sublist.mpr hy)
  exact hxy.trans (by simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil] using h.flatMap block)

theorem uniform_block_sublist_order {A B : Type*} (xs : List A) (block : A → List B)
    {a b : A} (ha : a∈xs) (hb : b∈xs) (hne : a≠b) :
    (∀ x∈block a, ∀ y∈block b, [x,y].Sublist (xs.flatMap block)) ∨
    (∀ x∈block a, ∀ y∈block b, [y,x].Sublist (xs.flatMap block)) := by
  rcases pair_sublist_or_reverse xs ha hb hne with h | h
  · exact Or.inl (fun x hx y hy => pair_sublist_flatMap xs block h hx hy)
  · exact Or.inr (fun x hx y hy => pair_sublist_flatMap xs block h hy hx)

def afterParentRow {A : Type*} [DecidableEq A] (row : List A) (parent : A) : List A :=
  row.drop (row.idxOf parent+1) ++ row.take (row.idxOf parent)

theorem afterParentInputs_eq_flatMap {A B : Type*} [DecidableEq A]
    (row : List A) (parent : A) (block : A → List B) :
    afterParentInputs row parent block=(afterParentRow row parent).flatMap block := by
  simp only [afterParentInputs,afterParentRow,List.flatMap_append]

theorem rotate_eq_cons_afterParentRow {A : Type*} [DecidableEq A]
    (row : List A) (parent : A) (hp : parent∈row) :
    row.rotate (row.idxOf parent)=parent::afterParentRow row parent := by
  have hi : row.idxOf parent<row.length := List.idxOf_lt_length_iff.mpr hp
  rw [List.rotate_eq_drop_append_take (Nat.le_of_lt hi),List.drop_eq_getElem_cons hi,List.getElem_idxOf hi]
  rfl

theorem mem_afterParentRow {A : Type*} [DecidableEq A] (row : List A) (parent : A)
    (hn : row.Nodup) (hp : parent∈row) (a : A) :
    a∈afterParentRow row parent ↔ a∈row ∧ a≠parent := by
  have he := rotate_eq_cons_afterParentRow row parent hp
  have hn' : (parent::afterParentRow row parent).Nodup := he ▸ List.nodup_rotate.mpr hn
  constructor
  · intro ha
    constructor
    · have hm : a∈parent::afterParentRow row parent := List.mem_cons_of_mem _ ha
      rw [←he,List.mem_rotate] at hm
      exact hm
    · intro h
      exact (List.nodup_cons.mp hn').1 (h ▸ ha)
  · rintro ⟨ha,hne⟩
    have hm : a∈row.rotate (row.idxOf parent) := List.mem_rotate.mpr ha
    rw [he,List.mem_cons] at hm
    exact hm.resolve_left hne

theorem idxOf_lt_of_pair_sublist {A : Type*} [DecidableEq A] (xs : List A)
    (hn : xs.Nodup) {a b : A} (h : [a,b].Sublist xs) : xs.idxOf a<xs.idxOf b := by
  have hp : xs.Pairwise (fun x y => xs.idxOf x<xs.idxOf y) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa only [List.idxOf_getElem hn i hi,List.idxOf_getElem hn j hj] using hij
  exact hp.forall_sublist h

end PlanarHom.PlanarityLRRealization
