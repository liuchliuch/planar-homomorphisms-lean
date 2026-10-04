import PlanarHom.PlanarityRowFaceTableMaterialization
import PlanarHom.PlanarityFaceOrientationCorrectness

/-! NEW actual returned face equations for the generic materialized-row compiler. -/
namespace PlanarHom.PlanarityRowFaceCode
open Complexity PlanarityLRRealization MultiGraph.Kasteleyn
 theorem boundedFaces_peelable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) :
    Peelable (boundaryById g rows) (boundedFaces g rows) :=
  PlanarityFaceCode.peelable_of_omitted_reachable (dualData g rows) (boundaryById g rows)
    (dualData_compatible g hg rows R hrows) (boundedFaces g rows)
    (fun _ hf=>boundedFace_reachable_from_omitted g hg rows R hrows hf)
 theorem boundedTable_faceOdd (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) :
    ∀f∈boundedFaces g rows,FaceOdd (logOrientation (computeOrientation (boundedTable g rows))) (boundaryById g rows f) := by
  rw [boundedTable_eq_faceTable,computeOrientation_semantics _ _ (boundedFaces_nodup g rows)]
  exact orientFaces_correct (boundaryById g rows) (boundedFaces g rows)
    (boundedFaces_nodup g rows) (boundedFaces_peelable g hg rows R hrows) (fun _=>true)
 theorem orientationLog_faceOdd (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) :
    ∀f∈boundedFaces g rows,FaceOdd (logOrientation (orientationLog g rows)) (boundaryById g rows f) :=
  boundedTable_faceOdd g hg rows R hrows
 theorem orientationLog_stored_faceOdd (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R)
    {q : RawFace} (hq : q∈boundedTable g rows) : FaceOdd (logOrientation (orientationLog g rows)) q.2 := by
  have hf : q.1∈boundedFaces g rows := List.mem_map.mpr ⟨q,hq,rfl⟩
  have hh := orientationLog_faceOdd g hg rows R hrows q.1 hf
  rw [fullTable_row g rows ((boundedTable_sublist g rows).subset hq)] at hh
  exact hh
end PlanarHom.PlanarityRowFaceCode
