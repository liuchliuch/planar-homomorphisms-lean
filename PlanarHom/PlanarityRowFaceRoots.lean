import PlanarHom.PlanarityRowFaceCodeProgram

/-! NEW unconditional exact per-component root selection facts. These are
combinatorial list facts and make no geometric exterior-face assertion. -/
namespace PlanarHom.PlanarityRowFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect

 theorem rootRepresentative_mem (g : MixedCode) (rows : Rows) {a : Dart}
    (ha : a∈representatives g rows) : rootRepresentative g rows a∈representatives g rows := by
  let xs := (representatives g rows).filter (fun b=>decide
    (componentRoot g (host g b)=componentRoot g (host g a)))
  have hmem : a∈xs := by simp [xs,ha]
  have hhead : xs.headD a∈xs := by
    cases h:xs with
    | nil => simp [h] at hmem
    | cons b bs => simp [h]
  exact (List.mem_filter.mp hhead).1

 theorem rootRepresentative_component (g : MixedCode) (rows : Rows) {a : Dart}
    (ha : a∈representatives g rows) :
    componentRoot g (host g (rootRepresentative g rows a))=componentRoot g (host g a) := by
  let xs := (representatives g rows).filter (fun b=>decide
    (componentRoot g (host g b)=componentRoot g (host g a)))
  have hmem : a∈xs := by simp [xs,ha]
  have hhead : xs.headD a∈xs := by
    cases h:xs with
    | nil => simp [h] at hmem
    | cons b bs => simp [h]
  exact of_decide_eq_true (List.mem_filter.mp hhead).2

 theorem rootRepresentative_eq_of_component (g : MixedCode) (rows : Rows) {a b : Dart}
    (ha : a∈representatives g rows)
    (hc : componentRoot g (host g a)=componentRoot g (host g b)) :
    rootRepresentative g rows a=rootRepresentative g rows b := by
  let xs := (representatives g rows).filter (fun c=>decide
    (componentRoot g (host g c)=componentRoot g (host g b)))
  have hm : a∈xs := by simp [xs,ha,hc]
  unfold rootRepresentative
  rw [hc]
  change xs.headD a=xs.headD b
  cases h:xs with
  | nil => simp [h] at hm
  | cons c cs => rfl

 theorem rootRepresentative_idempotent (g : MixedCode) (rows : Rows) {a : Dart}
    (ha : a∈representatives g rows) :
    rootRepresentative g rows (rootRepresentative g rows a)=rootRepresentative g rows a :=
   rootRepresentative_eq_of_component g rows (rootRepresentative_mem g rows ha)
     (rootRepresentative_component g rows ha)

 theorem rootRepresentative_unique (g : MixedCode) (rows : Rows) {a b : Dart}
    (ha : a∈representatives g rows)
    (hca : rootRepresentative g rows a=a) (hcb : rootRepresentative g rows b=b)
    (hc : componentRoot g (host g a)=componentRoot g (host g b)) : a=b := by
  rw [← hca,← hcb]
  exact rootRepresentative_eq_of_component g rows ha hc

end PlanarHom.PlanarityRowFaceCode
