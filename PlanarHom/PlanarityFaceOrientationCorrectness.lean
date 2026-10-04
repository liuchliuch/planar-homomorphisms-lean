import PlanarHom.PlanarityFaceTableMaterialization

/-! NEW correctness of the actual computed orientation on every emitted cycle
boundary. Connectivity, incidence and peeling are derived from the raw graph;
planarity and Pfaffian matching-sign correctness remain separate obligations. -/
namespace PlanarHom.PlanarityFaceCode
open Complexity PlanarityLRConstraints MultiGraph.Kasteleyn

 theorem peelable_of_omitted_reachable (D : DualIncidence ℕ ℕ) (boundary : Boundaries ℕ ℕ)
    (hc : D.Compatible boundary) (fs : List ℕ)
    (hconn : ∀f∈fs,∃r,r∉fs ∧ Relation.ReflTransGen D.Adj r f) : Peelable boundary fs := by
  intro us hsub hne
  obtain ⟨f,hf⟩:=List.exists_mem_of_ne_nil us hne
  obtain ⟨root,hr,hpath⟩:=hconn f (hsub f hf)
  obtain ⟨u,v,hu,hv,e,hedge⟩:=reach_crosses_cut D.Adj us root f hpath
    (fun h=>hr (hsub root h)) hf
  have huv:u≠v := fun h=>hu (h ▸ hv)
  refine ⟨v,hv,e,?_,?_⟩
  · rw [hc e v]
    rcases hedge with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;> simp [hl,hr,huv,huv.symm]
  · intro w hw hwv
    have huw:u≠w := fun h=>hu (h ▸ hw)
    rw [hc e w]
    rcases hedge with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;> simp [hl,hr,huw,hwv.symm]

 theorem boundedFaces_peelable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) : Peelable (boundaryById g bits) (boundedFaces g bits) :=
   peelable_of_omitted_reachable (dualData g bits) (boundaryById g bits)
     (dualData_compatible g hg bits) (boundedFaces g bits)
     (fun _ hf=>boundedFace_reachable_from_omitted g hg bits hf)

 theorem boundedTable_faceOdd (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) : ∀f∈boundedFaces g bits,
    FaceOdd (logOrientation (computeOrientation (boundedTable g bits))) (boundaryById g bits f) := by
  rw [boundedTable_eq_faceTable,computeOrientation_semantics _ _ (boundedFaces_nodup g bits)]
  exact orientFaces_correct (boundaryById g bits) (boundedFaces g bits)
    (boundedFaces_nodup g bits) (boundedFaces_peelable g hg bits) (fun _=>true)

 theorem orientationLog_faceOdd (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    ∀f∈boundedFaces g (decideAligned g).2,
      FaceOdd (logOrientation (orientationLog g)) (boundaryById g (decideAligned g).2 f) :=
   boundedTable_faceOdd g hg (decideAligned g).2

 theorem orientationLog_stored_faceOdd (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {q : RawFace} (hq : q∈computedBoundedTable g) :
    FaceOdd (logOrientation (orientationLog g)) q.2 := by
  have hf:q.1∈boundedFaces g (decideAligned g).2:=List.mem_map.mpr ⟨q,hq,rfl⟩
  have hh:=orientationLog_faceOdd g hg q.1 hf
  rw [fullTable_row g (decideAligned g).2 ((boundedTable_sublist g _).subset hq)] at hh
  exact hh

/-- Complete ordinary-input encoded runtime plus actual returned face equations. -/
 theorem certified_orientationLog :
    FP MixedCode.encoding logCode orientationLog ∧
    ∀(g : MixedCode) (bt ut : ℕ), g.Valid bt ut →
      ∀q∈computedBoundedTable g, FaceOdd (logOrientation (orientationLog g)) q.2 :=
   ⟨fp_orientationLog,fun g _ _ hg _ hq=>orientationLog_stored_faceOdd g hg hq⟩

end PlanarHom.PlanarityFaceCode
