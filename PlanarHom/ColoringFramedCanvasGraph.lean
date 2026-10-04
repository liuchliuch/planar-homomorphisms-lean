import PlanarHom.ColoringFramedSpliceProgram
import PlanarHom.ColoringCanvasRotationRows

/-! Canonical framed augmentation. All original coloring vertices remain;
exactly four fresh corner vertices are added per macro. Old macro edge
occurrences are the literal prefix of each framed macro edge table. -/
noncomputable section
open Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PlanarHom.ColoringEmitter
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree
namespace FramedMacro

theorem vertexCount_eq (s : CellShape) : vertexCount s=Macro.vertexCount s.kind+4 := by cases s <;> decide

def vertexParts (s : CellShape) : (LocalPatch.NumericVertex s⊕Fin 4)≃Fin (vertexCount s) :=
  finSumFinEquiv.trans (finCongr (vertexCount_eq s).symm)

def oldVertex (s : CellShape) (v : LocalPatch.NumericVertex s) : Fin (vertexCount s) := vertexParts s (.inl v)

theorem oldEdge_bound (s : CellShape) : (Macro.edges s.kind).length≤edgeCount s := by cases s <;> decide

def oldEdge (s : CellShape) (e : LocalPatch.Edge s) : Fin (edgeCount s) := Fin.castLE (oldEdge_bound s) e

end FramedMacro
namespace FramedCanvas

abbrev Vertex (f : NumericFormula) := Canvas.Vertex f ⊕ (Canvas.Index f×Fin 4)

def initialSignal (f : NumericFormula) (i : Fin f.1) : Boundary f :=
  ⟨(0,i.val),Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩

def seedVertex (f : NumericFormula) (e : Fin (3*f.1)) : Vertex f :=
  .inl (.inl (initialSignal f ⟨e.val/3,by have h:=e.isLt; omega⟩,
    ⟨2-e.val%3,by have h:=Nat.mod_lt e.val (by omega : 0<3); omega⟩))

def placeMacroVertex (f : NumericFormula) (i : Canvas.Index f)
    (v : Fin (FramedMacro.vertexCount (canvasCell f i).shape)) : Vertex f :=
  Sum.elim
    (fun w=>.inl (PortPatchAssembly.placeVertex (W:=Canvas.Private f) (Canvas.port f) i
      ((LocalPatch.localVertexParts (canvasCell f i).shape).symm w)))
    (fun k=>.inr (i,k)) ((FramedMacro.vertexParts (canvasCell f i).shape).symm v)

def graph (f : NumericFormula) : MultiGraph (Vertex f) (Edge f) where
  src
    | .inl e => seedVertex f e
    | .inr ⟨i,e⟩ => placeMacroVertex f i ((FramedMacro.graph (canvasCell f i).shape).src e)
  dst
    | .inl e => seedVertex f (finRotate (3*f.1) e)
    | .inr ⟨i,e⟩ => placeMacroVertex f i ((FramedMacro.graph (canvasCell f i).shape).dst e)

def oldEdge (f : NumericFormula) (e : Canvas.Edge f) : Edge f :=
  .inr ⟨e.1,FramedMacro.oldEdge (canvasCell f e.1).shape e.2⟩

def keepEdge (f : NumericFormula) : Edge f → Bool
  | .inl _ => false
  | .inr ⟨i,e⟩ => decide (e.val<(Macro.edges (canvasCell f i).shape.kind).length)

def keepDart (f : NumericFormula) : Dart f → Option (MultiGraph.Kasteleyn.Dart (Canvas.Edge f))
  | (.inl _,_) => none
  | (.inr ⟨i,e⟩,b) => if h:e.val<(Macro.edges (canvasCell f i).shape.kind).length then some (⟨i,⟨e.val,h⟩⟩,b) else none

def oldDart (f : NumericFormula) (a : MultiGraph.Kasteleyn.Dart (Canvas.Edge f)) : Dart f := (oldEdge f a.1,a.2)

@[simp] theorem keepDart_oldDart (f : NumericFormula) (a : MultiGraph.Kasteleyn.Dart (Canvas.Edge f)) :
    keepDart f (oldDart f a)=some a := by
  obtain ⟨⟨i,e⟩,b⟩:=a
  simp only [keepDart,oldDart,oldEdge,FramedMacro.oldEdge,Fin.coe_castLE,dif_pos e.isLt,Fin.eta]

theorem place_oldVertex (f : NumericFormula) (i : Canvas.Index f) (v : LocalPatch.NumericVertex (canvasCell f i).shape) :
    placeMacroVertex f i (FramedMacro.oldVertex (canvasCell f i).shape v)=
      .inl (PortPatchAssembly.placeVertex (W:=Canvas.Private f) (Canvas.port f) i
        ((LocalPatch.localVertexParts (canvasCell f i).shape).symm v)) := by
  simp only [placeMacroVertex,FramedMacro.oldVertex,Equiv.symm_apply_apply,Sum.elim_inl]

end FramedCanvas
end PlanarHom.ColoringEmitter
