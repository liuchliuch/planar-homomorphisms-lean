import PlanarHom.PlanarityRowFaceDualConnectivity

/-! NEW exact label list, root omission and table materialization facts. -/
namespace PlanarHom.PlanarityRowFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRRealization
open MultiGraph.Kasteleyn

 def boundedFaces (g : MixedCode) (rows : Rows) : List ℕ := (boundedTable g rows).map Prod.fst

 theorem faceId_of_getElem? (g : MixedCode) (rows : Rows) {a : PlanarityRotationCode.Dart} {f : ℕ}
    (hf : (representatives g rows)[f]?=some a) : faceId g rows a=f := by
  unfold faceId
  rw [representative_fixed_of_mem g rows (List.mem_of_getElem? hf)]
  obtain ⟨hi,he⟩:=List.getElem?_eq_some_iff.mp hf
  rw [← he]
  simpa only [dart_idxOf_decidable] using List.idxOf_getElem (representatives_nodup g rows) f hi

 theorem faceId_injective (g : MixedCode) (rows : Rows) {a b : PlanarityRotationCode.Dart}
    (ha : a∈representatives g rows) (hb : b∈representatives g rows)
    (h : faceId g rows a=faceId g rows b) : a=b := by
  apply (List.idxOf_inj ha hb).mp
  simpa only [faceId,representative_fixed_of_mem g rows ha,
    representative_fixed_of_mem g rows hb,dart_idxOf_decidable] using h

 theorem fullTable_row (g : MixedCode) (rows : Rows) {q : RawFace}
    (hq : q∈fullTable g rows) : boundaryById g rows q.1=q.2 := by
  obtain ⟨⟨a,i⟩,hi,rfl⟩:=List.mem_map.mp hq
  exact boundaryById_eq g rows ((List.mk_mem_zipIdx_iff_getElem?).mp hi)

 theorem fullTable_keys_nodup (g : MixedCode) (rows : Rows) :
    ((fullTable g rows).map Prod.fst).Nodup := by
  simp only [fullTable,List.map_map,Function.comp_def]
  change ((representatives g rows).zipIdx.map Prod.snd).Nodup
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' _

 theorem boundedFaces_nodup (g : MixedCode) (rows : Rows) : (boundedFaces g rows).Nodup :=
   (fullTable_keys_nodup g rows).sublist ((boundedTable_sublist g rows).map Prod.fst)

 theorem boundedTable_eq_faceTable (g : MixedCode) (rows : Rows) :
    boundedTable g rows=faceTable (boundaryById g rows) (boundedFaces g rows) := by
  unfold faceTable boundedFaces
  rw [List.map_map]
  conv_lhs => rw [← List.map_id (boundedTable g rows)]
  apply List.map_congr_left
  intro q hq
  exact Prod.ext rfl (fullTable_row g rows ((boundedTable_sublist g rows).subset hq)).symm

 theorem mem_boundedFaces_iff (g : MixedCode) (rows : Rows) (f : ℕ) :
    f∈boundedFaces g rows ↔ ∃a∈representatives g rows,
      rootRepresentative g rows a≠a ∧ faceId g rows a=f := by
  constructor
  · intro h
    obtain ⟨q,hq,hqf⟩:=List.mem_map.mp h
    obtain ⟨⟨a,i⟩,hi,rfl⟩:=List.mem_map.mp hq
    rcases List.mem_filter.mp hi with ⟨hai,hr⟩
    refine ⟨a,List.fst_mem_of_mem_zipIdx hai,of_decide_eq_true hr,?_⟩
    exact (faceId_of_getElem? g rows ((List.mk_mem_zipIdx_iff_getElem?).mp hai)).trans hqf
  · rintro ⟨a,ha,hr,hf⟩
    have hi : (a,faceId g rows a)∈(representatives g rows).zipIdx := by
      apply (List.mk_mem_zipIdx_iff_getElem?).mpr
      simpa only [faceId,representative_fixed_of_mem g rows ha,dart_idxOf_decidable] using List.getElem?_idxOf ha
    exact List.mem_map.mpr ⟨(faceId g rows a,boundary g rows a),
      List.mem_map.mpr ⟨(a,faceId g rows a),List.mem_filter.mpr ⟨hi,decide_eq_true hr⟩,rfl⟩,hf⟩

 theorem selectedRoot_not_mem (g : MixedCode) (rows : Rows) {a : PlanarityRotationCode.Dart}
    (ha : a∈representatives g rows) :
    faceId g rows (rootRepresentative g rows a)∉boundedFaces g rows := by
  intro hm
  obtain ⟨b,hb,hne,he⟩:=(mem_boundedFaces_iff g rows _).mp hm
  have hbr:=faceId_injective g rows hb (rootRepresentative_mem g rows ha) he
  subst b
  exact hne (rootRepresentative_idempotent g rows ha)

 theorem boundedFace_reachable_from_omitted (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) {f : ℕ} (hf : f∈boundedFaces g rows) :
    ∃r, r∉boundedFaces g rows ∧ Relation.ReflTransGen (dualData g rows).Adj r f := by
  obtain ⟨a,ha,_,he⟩:=(mem_boundedFaces_iff g rows f).mp hf
  refine ⟨faceId g rows (rootRepresentative g rows a),selectedRoot_not_mem g rows ha,?_⟩
  rw [← he]
  exact selectedRoot_reachable g hg rows R hrows ha

end PlanarHom.PlanarityRowFaceCode
