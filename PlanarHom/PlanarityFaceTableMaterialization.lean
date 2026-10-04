import PlanarHom.PlanarityFaceDualConnectivity

/-! NEW exact label list, root omission and table materialization facts. -/
namespace PlanarHom.PlanarityFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRRealization
open MultiGraph.Kasteleyn

 def boundedFaces (g : MixedCode) (bits : List Bool) : List ℕ := (boundedTable g bits).map Prod.fst

 theorem faceId_of_getElem? (g : MixedCode) (bits : List Bool) {a : PlanarityRotationCode.Dart} {f : ℕ}
    (hf : (representatives g bits)[f]?=some a) : faceId g bits a=f := by
  unfold faceId
  rw [representative_fixed_of_mem g bits (List.mem_of_getElem? hf)]
  obtain ⟨hi,he⟩:=List.getElem?_eq_some_iff.mp hf
  rw [← he]
  simpa only [dart_idxOf_decidable] using List.idxOf_getElem (representatives_nodup g bits) f hi

 theorem faceId_injective (g : MixedCode) (bits : List Bool) {a b : PlanarityRotationCode.Dart}
    (ha : a∈representatives g bits) (hb : b∈representatives g bits)
    (h : faceId g bits a=faceId g bits b) : a=b := by
  apply (List.idxOf_inj ha hb).mp
  simpa only [faceId,representative_fixed_of_mem g bits ha,
    representative_fixed_of_mem g bits hb,dart_idxOf_decidable] using h

 theorem fullTable_row (g : MixedCode) (bits : List Bool) {q : RawFace}
    (hq : q∈fullTable g bits) : boundaryById g bits q.1=q.2 := by
  obtain ⟨⟨a,i⟩,hi,rfl⟩:=List.mem_map.mp hq
  exact boundaryById_eq g bits ((List.mk_mem_zipIdx_iff_getElem?).mp hi)

 theorem fullTable_keys_nodup (g : MixedCode) (bits : List Bool) :
    ((fullTable g bits).map Prod.fst).Nodup := by
  simp only [fullTable,List.map_map,Function.comp_def]
  change ((representatives g bits).zipIdx.map Prod.snd).Nodup
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' _

 theorem boundedFaces_nodup (g : MixedCode) (bits : List Bool) : (boundedFaces g bits).Nodup :=
   (fullTable_keys_nodup g bits).sublist ((boundedTable_sublist g bits).map Prod.fst)

 theorem boundedTable_eq_faceTable (g : MixedCode) (bits : List Bool) :
    boundedTable g bits=faceTable (boundaryById g bits) (boundedFaces g bits) := by
  unfold faceTable boundedFaces
  rw [List.map_map]
  conv_lhs => rw [← List.map_id (boundedTable g bits)]
  apply List.map_congr_left
  intro q hq
  exact Prod.ext rfl (fullTable_row g bits ((boundedTable_sublist g bits).subset hq)).symm

 theorem mem_boundedFaces_iff (g : MixedCode) (bits : List Bool) (f : ℕ) :
    f∈boundedFaces g bits ↔ ∃a∈representatives g bits,
      rootRepresentative g bits a≠a ∧ faceId g bits a=f := by
  constructor
  · intro h
    obtain ⟨q,hq,hqf⟩:=List.mem_map.mp h
    obtain ⟨⟨a,i⟩,hi,rfl⟩:=List.mem_map.mp hq
    rcases List.mem_filter.mp hi with ⟨hai,hr⟩
    refine ⟨a,List.fst_mem_of_mem_zipIdx hai,of_decide_eq_true hr,?_⟩
    exact (faceId_of_getElem? g bits ((List.mk_mem_zipIdx_iff_getElem?).mp hai)).trans hqf
  · rintro ⟨a,ha,hr,hf⟩
    have hi : (a,faceId g bits a)∈(representatives g bits).zipIdx := by
      apply (List.mk_mem_zipIdx_iff_getElem?).mpr
      simpa only [faceId,representative_fixed_of_mem g bits ha,dart_idxOf_decidable] using List.getElem?_idxOf ha
    exact List.mem_map.mpr ⟨(faceId g bits a,boundary g bits a),
      List.mem_map.mpr ⟨(a,faceId g bits a),List.mem_filter.mpr ⟨hi,decide_eq_true hr⟩,rfl⟩,hf⟩

 theorem selectedRoot_not_mem (g : MixedCode) (bits : List Bool) {a : PlanarityRotationCode.Dart}
    (ha : a∈representatives g bits) :
    faceId g bits (rootRepresentative g bits a)∉boundedFaces g bits := by
  intro hm
  obtain ⟨b,hb,hne,he⟩:=(mem_boundedFaces_iff g bits _).mp hm
  have hbr:=faceId_injective g bits hb (rootRepresentative_mem g bits ha) he
  subst b
  exact hne (rootRepresentative_idempotent g bits ha)

 theorem boundedFace_reachable_from_omitted (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {f : ℕ} (hf : f∈boundedFaces g bits) :
    ∃r, r∉boundedFaces g bits ∧ Relation.ReflTransGen (dualData g bits).Adj r f := by
  obtain ⟨a,ha,_,he⟩:=(mem_boundedFaces_iff g bits f).mp hf
  refine ⟨faceId g bits (rootRepresentative g bits a),selectedRoot_not_mem g bits ha,?_⟩
  rw [← he]
  exact selectedRoot_reachable g hg bits ha

end PlanarHom.PlanarityFaceCode
