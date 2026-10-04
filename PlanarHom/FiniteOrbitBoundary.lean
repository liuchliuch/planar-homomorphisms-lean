import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! NEW bounded orbit truncation lemma. Every hypothesis below is a local
sequence fact; the computed dart application derives it from a finite permutation. -/
namespace PlanarHom.FiniteOrbitBoundary

theorem trim_prefix {A : Type*} [BEq A] [LawfulBEq A] (a : A) (xs ys : List A)
    (hx : a ∉ xs) (hy : ys=[] ∨ ∃ zs, ys=a::zs) :
    ((a::xs)++ys).take 1 ++ (((a::xs)++ys).tail.takeWhile (fun b => b != a)) = a::xs := by
  have hall : ∀ b ∈ xs, (b != a) = true := by
    intro b hb
    simp only [bne_iff_ne]
    intro h
    exact hx (h ▸ hb)
  simp only [List.cons_append,List.take_succ_cons,List.take_zero,List.tail_cons]
  rw [List.takeWhile_append_of_pos hall]
  rcases hy with rfl | ⟨zs,rfl⟩ <;> simp

/-- A bounded iterate list, cut at its first positive return, is exactly one
cycle, even when the bound is larger than the cycle length. -/
theorem trim_walk {A : Type*} [BEq A] [LawfulBEq A] (s : ℕ → A) (p N : ℕ)
    (hp : 0 < p) (hN : p ≤ N) (hret : s p=s 0)
    (hfirst : ∀ i, 0<i → i<p → s i≠s 0) :
    (((List.range N).map s).take 1 ++
      ((List.range N).map s).tail.takeWhile (fun b => b != s 0)) = (List.range p).map s := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hN
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hpref : (List.range (k+1)).map s = s 0 :: (List.range k).map (fun i => s (i+1)) := by
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Function.comp_def]
  have hnot : s 0 ∉ (List.range k).map (fun i => s (i+1)) := by
    intro h
    obtain ⟨i,hi,he⟩ := List.mem_map.mp h
    exact hfirst (i+1) (by omega) (by have := List.mem_range.mp hi; omega) he
  rw [List.range_add,List.map_append,hpref]
  apply trim_prefix _ _ _ hnot
  cases q with
  | zero => simp
  | succ q =>
      right
      rw [List.range_succ_eq_map]
      simp only [List.map_cons,List.map_map,Function.comp_def,Nat.add_zero,hret]
      exact ⟨_,rfl⟩

end PlanarHom.FiniteOrbitBoundary
