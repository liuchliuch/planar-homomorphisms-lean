import PlanarHom.PlanarityFaceCodeProgram

/-! NEW reconstruction. Raw face-step indices never grow: they either come from
an original occurrence or retain the queried dart. No valid-graph premise is used. -/
namespace PlanarHom.PlanarityFaceCode
open Complexity PlanarityRotationCode PlanarityLRDirect PlanarityLRRawConstraints PlanarityDepthFirstSearch

 theorem positive_height_valid (g : MixedCode) (v : ℕ) (h : 0<height g v) : v<g.vertices := by
  cases hf : (run g).discovered.find? (fun d=>d.vertex==v) with
  | none => simp [height,ancestors,discoveryAt,hf] at h
  | some d =>
    have hd:=List.mem_of_find?_eq_some hf
    have he: d.vertex=v := by simpa using List.find?_some hf
    have hv:=(run_goodSeen g).2 d.vertex (List.mem_map.mpr ⟨d,hd,rfl⟩)
    simpa only [he] using hv

 theorem incoming_index (g : MixedCode) (bits : List Bool) (e : ℕ) (side : Bool) {a : Dart}
    (h : a∈incoming g bits e side) : a.1<g.edges.length := by
  obtain ⟨b,hb,_,_,rfl⟩ := (mem_incoming g bits e side a).mp h
  simpa using (of_decide_eq_true hb).1

 theorem edgeBlock_index (g : MixedCode) (bits : List Bool) {e : ℕ} (he : e<g.edges.length)
    {a : Dart} (h : a∈edgeBlock g bits e) : a.1<g.edges.length := by
  simp only [edgeBlock,List.mem_append,List.mem_singleton] at h
  rcases h with (h | rfl) | h
  · exact incoming_index g bits e false h
  · exact he
  · exact incoming_index g bits e true h

 theorem directRow_index (g : MixedCode) (bits : List Bool) (v : ℕ) {a : Dart}
    (h : a∈directRow g bits v) : a.1<g.edges.length := by
  simp only [directRow,List.mem_append] at h
  rcases h with (h | h) | h
  · unfold parentRow at h
    split_ifs at h with hz
    · simp at h
    · have he : a=reverse (outward g (parentEdge g v)) := by simpa using h
      rw [he]
      exact parentEdge_lt g (positive_height_valid g v (by omega)) (by omega)
  · obtain ⟨e,he,ha⟩ := List.mem_flatMap.mp h
    exact edgeBlock_index g bits (outgoing_valid g v ((mem_orderedOutgoing g bits v e).mp he)) ha
  · obtain ⟨e,he,ha⟩ := List.mem_flatMap.mp h
    have hei:=List.mem_range.mp (List.mem_filter.mp he).1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl <;> exact hei

 theorem rowNext_index (row : List Dart) (a : Dart) (m : ℕ) (hr : ∀b∈row,b.1<m) :
    (rowNext row a).1<m ∨ (rowNext row a).1=a.1 := by
  unfold rowNext
  rw [List.getD_eq_getElem?_getD]
  cases h : row[(row.idxOf a+1)%row.length]? with
  | none => exact Or.inr rfl
  | some b => exact Or.inl (hr b (List.mem_of_getElem? h))

 theorem directRotation_index (g : MixedCode) (bits : List Bool) (a : Dart) :
    (directRotation g bits a).1<g.edges.length ∨ (directRotation g bits a).1=a.1 :=
  rowNext_index _ a _ (fun b hb=>directRow_index g bits _ hb)

 theorem faceStep_index (g : MixedCode) (bits : List Bool) (a : Dart) :
    (faceStep g bits a).1<g.edges.length ∨ (faceStep g bits a).1=a.1 :=
  directRotation_index g bits (reverse a)

 theorem faceStep_preserves (g : MixedCode) (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) :
    (faceStep g bits a).1<g.edges.length := by
  rcases faceStep_index g bits a with h | h
  · exact h
  · simpa only [h] using ha

end PlanarHom.PlanarityFaceCode
