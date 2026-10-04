import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Nodup

/-! NEW literal sublist transport across a cyclic cut. The rotation index is
the actual first occurrence, and the complementary suffix starts immediately
after the last selected input. No geometric or Euler premise is used. -/
namespace PlanarHom.FiniteCycleSublistCuts
variable {A:Type*} [DecidableEq A]

 theorem split_selected (pre post xs:List A) (a:A) (h:(pre++a::post).Sublist xs) :
    ∃left right,xs=left++a::right ∧ pre.Sublist left ∧ post.Sublist right := by
  obtain ⟨l,r,he,hpre,hs⟩:=List.append_sublist_iff.mp h
  obtain ⟨u,v,hr,ha,hpost⟩:=List.cons_sublist_iff.mp hs
  obtain ⟨s,t,hu⟩:=List.mem_iff_append.mp ha
  refine ⟨l++s,t++v,?_,hpre.trans (List.sublist_append_left l s),
    hpost.trans (List.sublist_append_right t v)⟩
  rw [he,hr,hu]
  simp only [List.append_assoc,List.cons_append]

 theorem idxOf_split {xs left right:List A} {a:A} (hn:xs.Nodup) (he:xs=left++a::right) :
    xs.idxOf a=left.length := by
  have hd:(left++a::right).Nodup:=he ▸ hn
  have ha:a∉left:=by
    intro ha
    exact List.disjoint_left.mp (List.disjoint_of_nodup_append hd) ha (List.mem_cons_self ..)
  rw [he,List.idxOf_append_of_notMem ha]
  simp

 theorem suffix_after_selected {pre post xs:List A} {a:A}
    (hn:xs.Nodup) (h:(pre++a::post).Sublist xs) :
    post.Sublist (xs.drop (xs.idxOf a+1)) := by
  obtain ⟨left,right,he,_,hp⟩:=split_selected pre post xs a h
  rw [idxOf_split hn he,he]
  simpa using hp

 theorem rotate_input_head {pre inputs post xs:List A} (hn:xs.Nodup) (hi:inputs≠[])
    (h:(pre++inputs++post).Sublist xs) :
    (inputs++post++pre).Sublist (xs.rotate (xs.idxOf (inputs.head hi))) := by
  cases inputs with
  | nil => exact (hi rfl).elim
  | cons a inputs =>
    obtain ⟨left,right,he,hpre,hpost⟩:=split_selected pre (inputs++post) xs a (by simpa [List.append_assoc] using h)
    rw [show (a::inputs).head hi=a from rfl,idxOf_split hn he,he,List.rotate_append_length_eq]
    simpa [List.append_assoc] using (hpost.cons₂ a).append hpre

 theorem complementary_arc {pre inputs post xs:List A} (hn:xs.Nodup) (hi:inputs≠[])
    (h:(pre++inputs++post).Sublist xs) :
    let rotated:=xs.rotate (xs.idxOf (inputs.head hi))
    (post++pre).Sublist (rotated.drop (rotated.idxOf (inputs.getLast hi)+1)) := by
  let rotated:=xs.rotate (xs.idxOf (inputs.head hi))
  have hr:rotated.Nodup:=List.nodup_rotate.mpr hn
  apply suffix_after_selected (pre:=inputs.dropLast) hr
  have hs:=rotate_input_head hn hi h
  have he:inputs.dropLast++inputs.getLast hi::(post++pre)=inputs++post++pre:=by
    calc
      _ = (inputs.dropLast++[inputs.getLast hi])++(post++pre) := by
        simp only [List.append_assoc,List.singleton_append]
      _ = _ := by rw [List.dropLast_concat_getLast hi,List.append_assoc]
  rw [he]
  exact hs

end PlanarHom.FiniteCycleSublistCuts
