import PlanarHom.CyclicRowCutUniqueness

/-! The concrete rotate-after-index cut really ends at the selected dart. -/
namespace PlanarHom
variable {D : Type} [BEq D] [LawfulBEq D]

 theorem rotate_after_idxOf_ending (xs : List D) (a : D) (hn : xs.Nodup) (ha : a∈xs) :
    ∃pre : List D,xs.rotate (xs.idxOf a+1)=pre++[a] := by
  obtain ⟨pre,post,he⟩ := List.append_of_mem ha
  have hnd : (pre++a::post).Nodup := by simpa only [←he] using hn
  have hnot : a∉pre := by
    intro hp
    exact (List.nodup_append.mp hnd).2.2 a hp a (by simp) rfl
  have hi : xs.idxOf a=pre.length := by
    rw [he,List.idxOf_append,if_neg hnot]
    simp
  have he' : xs=(pre++[a])++post := by simpa only [List.append_assoc,List.singleton_append] using he
  refine ⟨post++pre,?_⟩
  rw [hi,he']
  have hr := List.rotate_append_length_eq (pre++[a]) post
  simpa only [List.length_append,List.length_singleton,List.append_assoc] using hr
end PlanarHom
