import PlanarHom.FiniteBlockAllocation

/-! Literal occurrence indexing of flattened lists, including repeated equal
entries and empty blocks. This provides an actual finite-index equivalence. -/
noncomputable section
namespace PlanarHom.ListBlockIndexing
open PositiveBlockProgram
variable {A B : Type}

theorem ofFn_get_take (xs : List A) (n : ℕ) (hn : n≤xs.length) :
    List.ofFn (fun i : Fin n => xs.get (Fin.castLE hn i))=xs.take n := by
  apply List.ext_getElem
  · simp [List.length_take_of_le hn]
  · intro i hi hj
    simp [List.getElem_ofFn,List.get_eq_getElem]

theorem total_length (xs : List A) (f : A → List B) :
    (∑ i : Fin xs.length,(f (xs.get i)).length)=(xs.flatMap f).length := by
  rw [sum_get xs (fun a => (f a).length)]
  simp

def equiv (xs : List A) (f : A → List B) :
    ((i : Fin xs.length) × Fin (f (xs.get i)).length) ≃ Fin (xs.flatMap f).length :=
  finSigmaFinEquiv.trans (finCongr (total_length xs f))

theorem prefix_length (xs : List A) (f : A → List B) (i : Fin xs.length) :
    (∑ j : Fin i.val,(f (xs.get (Fin.castLE i.isLt.le j))).length)=((xs.take i.val).flatMap f).length := by
  rw [←List.sum_ofFn]
  have he : List.ofFn (fun j : Fin i.val => (f (xs.get (Fin.castLE i.isLt.le j))).length)=
      (xs.take i.val).map (fun x => (f x).length) := by
    change List.ofFn ((fun x => (f x).length) ∘ (fun j : Fin i.val => xs.get (Fin.castLE i.isLt.le j)))=_
    rw [←List.map_ofFn,ofFn_get_take]
  rw [he]
  simp

@[simp] theorem equiv_val (xs : List A) (f : A → List B)
    (p : (i : Fin xs.length) × Fin (f (xs.get i)).length) :
    (equiv xs f p).val=((xs.take p.1.val).flatMap f).length+p.2.val := by
  simp only [equiv,Equiv.trans_apply,finCongr_apply,Fin.coe_cast,finSigmaFinEquiv_apply,prefix_length]

private theorem get_append_offset (as bs : List B) (i : ℕ) :
    (as++bs)[as.length+i]?=bs[i]? := by
  simp [List.getElem?_append_right]

/-- A flat list reads the same physical occurrence at its prefix-length address. -/
theorem get_flatMap_at (xs : List A) (f : A → List B)
    (i : Fin xs.length) (j : Fin (f (xs.get i)).length) :
    (xs.flatMap f)[((xs.take i.val).flatMap f).length+j.val]?=some ((f (xs.get i)).get j) := by
  induction xs with
  | nil => exact i.elim0
  | cons a xs ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero,List.take_zero,List.flatMap_nil,List.length_nil,Nat.zero_add,List.flatMap_cons]
      rw [List.getElem?_append_left (by simpa using j.isLt)]
      simp
    | succ i =>
      change (f a++xs.flatMap f)[(f a++(xs.take i.val).flatMap f).length+j.val]?=some ((f (xs.get i)).get j)
      rw [List.length_append,Nat.add_assoc,get_append_offset]
      exact ih i j

/-- The canonical equivalence preserves the actual element at every occurrence. -/
theorem get_equiv (xs : List A) (f : A → List B)
    (p : (i : Fin xs.length) × Fin (f (xs.get i)).length) :
    (xs.flatMap f).get (equiv xs f p)=(f (xs.get p.1)).get p.2 := by
  have h := get_flatMap_at xs f p.1 p.2
  rw [←equiv_val xs f p] at h
  rw [List.getElem?_eq_getElem (equiv xs f p).isLt] at h
  exact Option.some.inj h

end PlanarHom.ListBlockIndexing
