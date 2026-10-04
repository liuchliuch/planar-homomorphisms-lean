import PlanarHom.PortPatchRowPreimage

/-! A reverse-ordered scan with exactly two nonempty contributors has the
literal two-block concatenation in that order. -/
namespace PlanarHom
variable {A B : Type} [DecidableEq A] {r : A→A→Prop}

 theorem select_two_words (ls : List A) (hn : ls.Nodup) (ho : ls.Pairwise r)
    (a b : A) (hne : a≠b) (ha : a∈ls) (hb : b∈ls) (hba : ¬r b a)
    (u v : List B) :
    ls.flatMap (fun x=>if x=a then u else if x=b then v else [])=u++v := by
  induction ls with
  | nil => simp at ha
  | cons c cs ih =>
      have hc := List.nodup_cons.mp hn
      have hr := List.pairwise_cons.mp ho
      by_cases hca : c=a
      · subst c
        have hbt : b∈cs := (List.mem_cons.mp hb).resolve_left hne.symm
        simp only [List.flatMap_cons,if_pos rfl]
        have he : cs.flatMap (fun x=>if x=a then u else if x=b then v else [])=
            cs.flatMap (fun x=>if x=b then v else []) := by
          apply List.flatMap_congr
          intro x hx
          rw [if_neg (by intro he; subst x; exact hc.1 hx)]
        rw [he,PortPatchAssembly.selectWord_eq cs hc.2 b hbt (fun _=>v)]
        simp
      · by_cases hcb : c=b
        · subst c
          have hat : a∈cs := (List.mem_cons.mp ha).resolve_left hne
          exact (hba (hr.1 a hat)).elim
        · have hat : a∈cs := (List.mem_cons.mp ha).resolve_left (Ne.symm hca)
          have hbt : b∈cs := (List.mem_cons.mp hb).resolve_left (Ne.symm hcb)
          simp only [List.flatMap_cons,if_neg hca,if_neg hcb,List.nil_append]
          exact ih hc.2 hr.2 hat hbt
end PlanarHom
