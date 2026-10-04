import Mathlib.Data.List.Range
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-! NEW exact finite even/odd index-word decompositions. -/
namespace PlanarHom

theorem range_pair_flatMap (n : ℕ) :
    (List.range n).flatMap (fun i=>[2*i,2*i+1])=List.range (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ,List.flatMap_append]
      simp only [List.flatMap_singleton]
      rw [ih,show 2*(n+1)=2*n+2 by omega,List.range_add]
      simp [List.range_succ]

theorem map_pair_partition_perm {A B : Type*} (xs : List A) (f g : A→B) :
    (xs.map f++xs.map g).Perm (xs.flatMap (fun a=>[f a,g a])) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons,List.flatMap_cons,List.cons_append,List.singleton_append]
      apply List.Perm.cons
      exact (List.perm_middle).trans (ih.cons (g a))

theorem even_odd_range_perm (n : ℕ) :
    ((List.range n).map (fun i=>2*i)++(List.range n).map (fun i=>2*i+1)).Perm (List.range (2*n)) := by
  rw [←range_pair_flatMap]
  exact map_pair_partition_perm _ _ _

end PlanarHom
