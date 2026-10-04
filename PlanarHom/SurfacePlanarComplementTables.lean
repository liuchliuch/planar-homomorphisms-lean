import PlanarHom.SurfacePlanarComplementProgram

/-! NEW exact table lookups and finite well-formedness of the planar compiler. -/
namespace PlanarHom.SurfacePlanarCompiler
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PlanarityRowFaceCode
open SurfaceRawEmbedding

 theorem pair_table_length {A : Type*} (f:ℕ→Bool→A) (n:ℕ) :
    ((List.range n).flatMap (fun e=>[f e false,f e true])).length=2*n := by
  simp [List.length_flatMap,Nat.mul_comm]

 theorem pair_table_get {A : Type*} (f:ℕ→Bool→A) (n e:ℕ) (he:e<n) (b:Bool) :
    ((List.range n).flatMap (fun e=>[f e false,f e true]))[2*e+(if b then 1 else 0)]?=some (f e b) := by
  induction n with
  | zero=>omega
  | succ n ih=>
    rw [List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    by_cases h:e<n
    · rw [List.getElem?_append_left (by rw [pair_table_length]; cases b <;> simp <;> omega)]
      exact ih h
    · have hen:e=n:=by omega
      subst e
      rw [List.getElem?_append_right (by rw [pair_table_length]; cases b <;> simp <;> omega)]
      rw [pair_table_length]
      cases b <;> simp

 theorem complement_dartLabel (ambient : ℕ) (g:MixedCode) (rs:Rows) (a:Dart (Fin g.edges.length)) :
    (complement ambient g rs).dartLabel a=region g rs (eraseDart a) := by
  unfold ComplementCode.dartLabel complement dartIndex
  dsimp only
  rw [pair_table_get (fun e b=>region g rs (e,b)) _ _ a.1.isLt a.2]
  rfl

 theorem complement_isolatedLabel (ambient : ℕ) (g:MixedCode) (rs:Rows) (v:ℕ) :
    (complement ambient g rs).isolatedLabel v=0 := by
  unfold ComplementCode.isolatedLabel complement
  rw [List.getElem?_map]
  cases (List.range g.vertices)[v]? <;> rfl

 theorem region_lt (g:MixedCode) {bt ut:ℕ} (hg:g.Valid bt ut) (rs:Rows)
    (R:RotationRows (g.toMultiGraph hg)) (hrs:Realizes g hg rs R) (a:Dart (Fin g.edges.length)) :
    region g rs (eraseDart a)<(disks g rs).length+1 := by
  unfold region
  dsimp only
  split
  · omega
  · rename_i hn
    have hm:representative g rs (eraseDart a)∈disks g rs := by
      simp only [disks,List.mem_filter,decide_eq_true_eq]
      exact ⟨representative_mem_representatives g hg rs R hrs a,hn⟩
    have h:=List.idxOf_lt_length_of_mem hm
    omega

 theorem region_face_step (g:MixedCode) {bt ut:ℕ} (hg:g.Valid bt ut) (rs:Rows)
    (R:RotationRows (g.toMultiGraph hg)) (hrs:Realizes g hg rs R) (a:Dart (Fin g.edges.length)) :
    region g rs (eraseDart (R.facePerm a))=region g rs (eraseDart a) := by
  unfold region
  rw [representative_eq_of_sameCycle g hg rs R hrs _ a Equiv.Perm.SameCycle.rfl.apply_left]

 theorem complement_wellFormed (ambient:ℕ) (g:MixedCode) {bt ut:ℕ} (hg:g.Valid bt ut) (rs:Rows)
    (R:RotationRows (g.toMultiGraph hg)) (hrs:Realizes g hg rs R) :
    (complement ambient g rs).WellFormed g hg R where
  regions_pos:=by rw [complement_regions]; omega
  dart_length:=complement_dart_length ambient g rs
  isolated_length:=complement_isolated_length ambient g rs
  dart_bound a:=by rw [complement_dartLabel,complement_regions]; exact region_lt g hg rs R hrs a
  face_step a:=by simp only [complement_dartLabel]; exact region_face_step g hg rs R hrs a
  isolated_bound v:=by rw [complement_isolatedLabel,complement_regions]; omega

 theorem complement_genus_value (ambient:ℕ) (g:MixedCode) (rs:Rows)
    (j:Fin (complement ambient g rs).genera.length) :
    (complement ambient g rs).genera[j.val]?.getD 0=if j.val=0 then ambient else 0 := by
  unfold complement
  cases h:j.val with
  | zero=>simp
  | succ k=>
    simp only [List.getElem?_cons_succ,Nat.succ_ne_zero,ite_false,List.getElem?_map]
    cases (disks g rs)[k]? <;> rfl

 theorem complement_genus_sum (ambient:ℕ) (g:MixedCode) (rs:Rows) :
    (∑j:Fin (complement ambient g rs).genera.length,(complement ambient g rs).genera[j.val]?.getD 0)=ambient := by
  simp_rw [complement_genus_value]
  have hp:0<(complement ambient g rs).genera.length:=by rw [complement_regions]; omega
  have he (j:Fin (complement ambient g rs).genera.length):j.val=0 ↔ j=⟨0,hp⟩ := ⟨fun h=>Fin.ext h,fun h=>congrArg Fin.val h⟩
  simp_rw [he]
  simp

end PlanarHom.SurfacePlanarCompiler
