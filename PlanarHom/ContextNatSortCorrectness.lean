import PlanarHom.PlanarityLRConstraintMachines
import Mathlib.Data.List.Sort

/-! NEW reconstruction. Literal partition-insertion sorting of natural labels,
with exact permutation/sortedness and equality to the existing mergeSort.
The later compiler uses this materialized bounded-fold implementation. -/
namespace PlanarHom.ContextNatSortMachines
variable {C : Type}

def insert (cmp : C→ℕ→ℕ→Bool) (c : C) (x : ℕ) (xs : List ℕ) : List ℕ :=
  xs.filter (fun y=>!(cmp c x y)) ++ x::xs.filter (cmp c x)

def sort (cmp : C→ℕ→ℕ→Bool) (c : C) (xs : List ℕ) : List ℕ :=
  xs.foldl (fun acc x=>insert cmp c x acc) []

 theorem insert_perm (cmp : C→ℕ→ℕ→Bool) (c : C) (x : ℕ) (xs : List ℕ) :
    (insert cmp c x xs).Perm (x::xs) := by
  have hh:=List.filter_append_perm (fun y=>!(cmp c x y)) xs
  simp only [Bool.not_not] at hh
  exact List.perm_middle.trans (hh.cons x)

 theorem fold_perm (cmp : C→ℕ→ℕ→Bool) (c : C) (xs acc : List ℕ) :
    (xs.foldl (fun acc x=>insert cmp c x acc) acc).Perm (xs.reverse++acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    have hh:=(ih (insert cmp c x acc)).trans ((List.Perm.refl xs.reverse).append (insert_perm cmp c x acc))
    simpa [List.reverse_cons,List.append_assoc] using hh

 theorem sort_perm (cmp : C→ℕ→ℕ→Bool) (c : C) (xs : List ℕ) : (sort cmp c xs).Perm xs := by
  have hh:=fold_perm cmp c xs []
  simp only [List.append_nil] at hh
  exact hh.trans (List.reverse_perm xs)

 theorem insert_sorted (cmp : C→ℕ→ℕ→Bool) (c : C)
    (ht : ∀a b,(cmp c a b || cmp c b a)=true)
    (htrans : ∀a b d,cmp c a b=true→cmp c b d=true→cmp c a d=true)
    (x : ℕ) (xs : List ℕ) (hs : xs.Pairwise (fun a b=>cmp c a b=true)) :
    (insert cmp c x xs).Pairwise (fun a b=>cmp c a b=true) := by
  have hleft (a : ℕ) (ha : a∈xs.filter (fun y=>!(cmp c x y))) : cmp c a x=true := by
    have hxa : cmp c x a=false := by simpa only [Bool.not_eq_true'] using (List.mem_filter.mp ha).2
    simpa [hxa] using ht x a
  apply List.pairwise_append.mpr
  refine ⟨hs.sublist List.filter_sublist,?_,?_⟩
  · apply List.pairwise_cons.mpr
    exact ⟨fun y hy=>(List.mem_filter.mp hy).2,hs.sublist List.filter_sublist⟩
  · intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hleft a ha
    · exact htrans a x b (hleft a ha) (List.mem_filter.mp hb).2

 theorem fold_sorted (cmp : C→ℕ→ℕ→Bool) (c : C)
    (ht : ∀a b,(cmp c a b || cmp c b a)=true)
    (htrans : ∀a b d,cmp c a b=true→cmp c b d=true→cmp c a d=true)
    (xs acc : List ℕ) (hs : acc.Pairwise (fun a b=>cmp c a b=true)) :
    (xs.foldl (fun acc x=>insert cmp c x acc) acc).Pairwise (fun a b=>cmp c a b=true) := by
  induction xs generalizing acc with
  | nil => exact hs
  | cons x xs ih => exact ih _ (insert_sorted cmp c ht htrans x acc hs)

 theorem sort_eq_mergeSort (cmp : C→ℕ→ℕ→Bool) (c : C)
    (ht : ∀a b,(cmp c a b || cmp c b a)=true)
    (htrans : ∀a b d,cmp c a b=true→cmp c b d=true→cmp c a d=true)
    (hanti : ∀a b,cmp c a b=true→cmp c b a=true→a=b) (xs : List ℕ) :
    sort cmp c xs=xs.mergeSort (cmp c) := by
  let r : ℕ→ℕ→Prop:=fun a b=>cmp c a b=true
  letI : IsAntisymm ℕ r := ⟨hanti⟩
  have hp:=(sort_perm cmp c xs).trans (List.mergeSort_perm xs (cmp c)).symm
  exact List.eq_of_perm_of_sorted (r:=r) hp
    (fold_sorted cmp c ht htrans xs [] (by simp)) (List.sorted_mergeSort htrans ht xs)

end PlanarHom.ContextNatSortMachines
