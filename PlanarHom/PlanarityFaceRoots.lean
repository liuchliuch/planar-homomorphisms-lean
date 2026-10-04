import PlanarHom.PlanarityFaceRootProgram

/-! NEW unconditional exact per-component root selection facts. These are
combinatorial list facts and make no geometric exterior-face assertion. -/
namespace PlanarHom.PlanarityFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect

 theorem rootRepresentative_mem (g : MixedCode) (bits : List Bool) {a : Dart}
    (ha : a∈representatives g bits) : rootRepresentative g bits a∈representatives g bits := by
  let xs := (representatives g bits).filter (fun b=>decide
    (componentRoot g (host g b)=componentRoot g (host g a)))
  have hmem : a∈xs := by simp [xs,ha]
  have hhead : xs.headD a∈xs := by
    cases h:xs with
    | nil => simp [h] at hmem
    | cons b bs => simp [h]
  exact (List.mem_filter.mp hhead).1

 theorem rootRepresentative_component (g : MixedCode) (bits : List Bool) {a : Dart}
    (ha : a∈representatives g bits) :
    componentRoot g (host g (rootRepresentative g bits a))=componentRoot g (host g a) := by
  let xs := (representatives g bits).filter (fun b=>decide
    (componentRoot g (host g b)=componentRoot g (host g a)))
  have hmem : a∈xs := by simp [xs,ha]
  have hhead : xs.headD a∈xs := by
    cases h:xs with
    | nil => simp [h] at hmem
    | cons b bs => simp [h]
  exact of_decide_eq_true (List.mem_filter.mp hhead).2

 theorem rootRepresentative_eq_of_component (g : MixedCode) (bits : List Bool) {a b : Dart}
    (ha : a∈representatives g bits)
    (hc : componentRoot g (host g a)=componentRoot g (host g b)) :
    rootRepresentative g bits a=rootRepresentative g bits b := by
  let xs := (representatives g bits).filter (fun c=>decide
    (componentRoot g (host g c)=componentRoot g (host g b)))
  have hm : a∈xs := by simp [xs,ha,hc]
  unfold rootRepresentative
  rw [hc]
  change xs.headD a=xs.headD b
  cases h:xs with
  | nil => simp [h] at hm
  | cons c cs => rfl

 theorem rootRepresentative_idempotent (g : MixedCode) (bits : List Bool) {a : Dart}
    (ha : a∈representatives g bits) :
    rootRepresentative g bits (rootRepresentative g bits a)=rootRepresentative g bits a :=
   rootRepresentative_eq_of_component g bits (rootRepresentative_mem g bits ha)
     (rootRepresentative_component g bits ha)

 theorem rootRepresentative_unique (g : MixedCode) (bits : List Bool) {a b : Dart}
    (ha : a∈representatives g bits)
    (hca : rootRepresentative g bits a=a) (hcb : rootRepresentative g bits b=b)
    (hc : componentRoot g (host g a)=componentRoot g (host g b)) : a=b := by
  rw [← hca,← hcb]
  exact rootRepresentative_eq_of_component g bits ha hc

end PlanarHom.PlanarityFaceCode
