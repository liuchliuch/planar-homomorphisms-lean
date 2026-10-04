import PlanarHom.ReplicationIndexEquiv

/-! An explicit stable index bijection for list filtering. Occurrences are
indexed before filtering, so equal values never collapse. -/

namespace PlanarHom.FilteredOccurrence

def positions {α : Type*} (xs : List α) (p : α → Bool) : List (Fin xs.length) :=
  (List.finRange xs.length).filter (fun i => p (xs.get i))

theorem positions_nodup {α : Type*} (xs : List α) (p : α → Bool) :
    (positions xs p).Nodup := (List.nodup_finRange _).filter _

@[simp] theorem mem_positions {α : Type*} (xs : List α) (p : α → Bool) (i : Fin xs.length) :
    i ∈ positions xs p ↔ p (xs.get i)=true := by simp [positions]

theorem map_positions {α : Type*} (xs : List α) (p : α → Bool) :
    (positions xs p).map xs.get = xs.filter p := by
  change ((List.finRange xs.length).filter (p ∘ xs.get)).map xs.get = _
  rw [← List.filter_map]
  have he : (List.finRange xs.length).map xs.get = xs := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  rw [he]

theorem length_positions {α : Type*} (xs : List α) (p : α → Bool) :
    (positions xs p).length = (xs.filter p).length := by
  simpa using congrArg List.length (map_positions xs p)

/-- The inverse is the verified list-index lookup from a duplicate-free list
of original positions, rather than an arbitrary cardinality bijection. -/
def equiv {α : Type*} (xs : List α) (p : α → Bool) :
    Fin (xs.filter p).length ≃ {i : Fin xs.length // p (xs.get i)=true} :=
  ((finCongr (length_positions xs p).symm).trans
    ((positions_nodup xs p).getEquiv)).trans
      (Equiv.subtypeEquivRight (fun i => mem_positions xs p i))

theorem get_equiv {α : Type*} (xs : List α) (p : α → Bool) (j : Fin (xs.filter p).length) :
    (xs.filter p).get j = xs.get (equiv xs p j).val := by
  have hi : j.val < (positions xs p).length := by
    rw [length_positions]; exact j.isLt
  have he := congrArg (fun ys : List α => ys[j.val]?) (map_positions xs p)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem j.isLt, Option.map_some] at he
  exact (Option.some.inj he).symm

end PlanarHom.FilteredOccurrence
