import PlanarHom.ColoringFramedCanvasRetention
import PlanarHom.ColoringEmitterMacroRows

noncomputable section
namespace PlanarHom.ColoringEmitter
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree
namespace MacroRows

theorem localRows_row (s : CellShape) (v : LocalPatch.Port s⊕LocalPatch.Private s) :
    (localRows s).row v=(numericRows s).row (LocalPatch.localVertexParts s v) := by
  change ((numericRows s).row (LocalPatch.localVertexParts s v)).map id=_
  exact List.map_id _

end MacroRows
namespace FramedMacro

def keepDart (s : CellShape) (a : Dart (Fin (edgeCount s))) : Option (Dart (LocalPatch.Edge s)) :=
  if h:a.1.val<(Macro.edges s.kind).length then some (⟨a.1.val,h⟩,a.2) else none

def oldDart (s : CellShape) (a : Dart (LocalPatch.Edge s)) : Dart (Fin (edgeCount s)) := (oldEdge s a.1,a.2)

@[simp] theorem keepDart_oldDart (s : CellShape) (a : Dart (LocalPatch.Edge s)) :
    keepDart s (oldDart s a)=some a := by
  obtain ⟨e,b⟩:=a
  simp only [keepDart,oldDart,oldEdge,Fin.coe_castLE,dif_pos e.isLt,Fin.eta]

theorem keepDart_partial_injective (s : CellShape)
    (a b : Dart (Fin (edgeCount s))) (y : Dart (LocalPatch.Edge s))
    (ha : keepDart s a=some y) (hb : keepDart s b=some y) : a=b := by
  unfold keepDart at ha hb
  split_ifs at ha hb
  have he:=(Option.some.inj ha).trans (Option.some.inj hb).symm
  exact Prod.ext (Fin.ext (congrArg (fun d : Dart (LocalPatch.Edge s)=>d.1.val) he))
    (congrArg (fun d : Dart (LocalPatch.Edge s)=>d.2) he)

end FramedMacro
namespace FramedCanvas

def sourceDart (f : NumericFormula) (i : Canvas.Index f) (a : MultiGraph.Kasteleyn.Dart (LocalPatch.Edge (canvasCell f i).shape)) :
    MultiGraph.Kasteleyn.Dart (Canvas.Edge f) := (⟨i,a.1⟩,a.2)

theorem keepDart_patchDart (f : NumericFormula) (i : Canvas.Index f) (a : MultiGraph.Kasteleyn.Dart (PatchEdge f i)) :
    keepDart f (patchDart f i a)=(FramedMacro.keepDart (canvasCell f i).shape a).map (sourceDart f i) := by
  obtain ⟨e,b⟩:=a
  by_cases h : e.val<(Macro.edges (canvasCell f i).shape.kind).length
  all_goals simp [patchDart,keepDart,FramedMacro.keepDart,sourceDart,h]

theorem keepDart_seedDart (f : NumericFormula) (a : MultiGraph.Kasteleyn.Dart (Fin (3*f.1))) :
    keepDart f (seedDart f a)=none := rfl

theorem filter_patchDart (f : NumericFormula) (i : Canvas.Index f) (xs : List (MultiGraph.Kasteleyn.Dart (PatchEdge f i))) :
    (xs.map (patchDart f i)).filterMap (keepDart f)=
      (xs.filterMap (FramedMacro.keepDart (canvasCell f i).shape)).map (sourceDart f i) := by
  rw [List.filterMap_map,List.map_filterMap]
  apply List.filterMap_congr
  intro a _
  exact keepDart_patchDart f i a

theorem filter_seedDart (f : NumericFormula) (xs : List (MultiGraph.Kasteleyn.Dart (Fin (3*f.1)))) :
    (xs.map (seedDart f)).filterMap (keepDart f)=[] := by
  rw [List.filterMap_map]
  apply List.filterMap_eq_nil_iff.mpr
  intro a _
  rfl

end FramedCanvas
end PlanarHom.ColoringEmitter
