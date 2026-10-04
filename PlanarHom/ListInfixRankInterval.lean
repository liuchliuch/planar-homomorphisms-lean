import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

/-! NEW finite rank separation for a literal contiguous block in a duplicate-free word. -/
namespace PlanarHom.ListInfixRankInterval

theorem rank_window {A : Type*} [DecidableEq A] {inside xs : List A}
    (hin : inside <:+: xs) (hn : xs.Nodup) :
    ∃lo, (∀a∈inside,lo≤xs.idxOf a ∧ xs.idxOf a<lo+inside.length) ∧
      (∀b∈xs,b∉inside→xs.idxOf b<lo ∨ lo+inside.length≤xs.idxOf b) := by
  obtain ⟨pre,post,rfl⟩ := hin
  simp only [List.append_assoc] at hn ⊢
  have hd := (List.nodup_append.mp hn).2.2
  have hinner : (inside++post).Nodup := (List.nodup_append.mp hn).2.1
  have hd' := (List.nodup_append.mp hinner).2.2
  refine ⟨pre.length,?_,?_⟩
  · intro a ha
    have hp : a∉pre := fun h=>hd a h a (List.mem_append_left _ ha) rfl
    rw [List.idxOf_append_of_notMem hp,List.idxOf_append_of_mem ha]
    have hh := List.idxOf_lt_length_iff.mpr ha
    omega
  · intro b hb hnot
    rcases List.mem_append.mp hb with hb | hb
    · left
      rw [List.idxOf_append_of_mem hb]
      exact List.idxOf_lt_length_iff.mpr hb
    · have hbpost : b∈post := (List.mem_append.mp hb).resolve_left hnot
      have hp : b∉pre := fun h=>hd b h b hb rfl
      right
      rw [List.idxOf_append_of_notMem hp,List.idxOf_append_of_notMem hnot]
      omega

theorem outside_rank_separation {A : Type*} [DecidableEq A] {inside xs : List A}
    (hin : inside <:+: xs) (hn : xs.Nodup) {a b c : A}
    (ha : a∈inside) (hc : c∈inside) (hb : b∈xs) (hout : b∉inside) :
    (xs.idxOf b<xs.idxOf a ∧ xs.idxOf b<xs.idxOf c) ∨
      (xs.idxOf a<xs.idxOf b ∧ xs.idxOf c<xs.idxOf b) := by
  obtain ⟨lo,hi,ho⟩ := rank_window hin hn
  have hia:=hi a ha
  have hic:=hi c hc
  rcases ho b hb hout with h | h
  · exact Or.inl ⟨by omega,by omega⟩
  · exact Or.inr ⟨by omega,by omega⟩

theorem sublist_middle_mem {A : Type*} [DecidableEq A] {inside xs : List A}
    (hin : inside <:+: xs) (hn : xs.Nodup) {a b c : A}
    (hsub : [a,b,c].Sublist xs) (ha : a∈inside) (hc : c∈inside) : b∈inside := by
  have hr : xs.Pairwise (fun x y=>xs.idxOf x<xs.idxOf y) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa only [List.idxOf_getElem hn] using hij
  have hs := hr.sublist hsub
  have hab := (List.pairwise_cons.mp hs).1 b (by simp)
  have hbc := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 c (by simp)
  by_contra hb
  have hbm : b∈xs := hsub.subset (by simp)
  rcases outside_rank_separation hin hn ha hc hbm hb with h | h <;> omega

end PlanarHom.ListInfixRankInterval
