import PlanarHom.ColoringFramedTypedRows
import PlanarHom.ColoringEmitterLocalPatches
import PlanarHom.ColoringCanvasFrontiers

/-! NEW uniform access to the four certified framed macros, keeping the
original cell-shape port order and the physical vertical triple order explicit. -/
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
open Classical
namespace PlanarHom.ColoringEmitter.FramedMacro
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles PositiveBlockProgram

 def vertexCount : CellShape→ℕ
  | .wireTop | .wireBottom | .wireDown => 534
  | .cross => 1274
  | .fan => 1058
  | .test => 118
 def edgeCount : CellShape→ℕ
  | .wireTop | .wireBottom | .wireDown => 1323
  | .cross => 3168
  | .fan => 2632
  | .test => 285
 def leftCount : CellShape→ℕ
  | .wireTop | .wireBottom | .wireDown | .fan => 3
  | .cross => 6
  | .test => 9
 def rightCount : CellShape→ℕ
  | .wireTop | .wireBottom | .wireDown => 3
  | .cross | .fan => 6
  | .test => 0

 def graph : (s : CellShape)→MultiGraph (Fin (vertexCount s)) (Fin (edgeCount s))
  | .wireTop | .wireBottom | .wireDown => ColoringMacroFaces.WireFramed.framedGraph
  | .cross => ColoringMacroFaces.CrossFramed.framedGraph
  | .fan => ColoringMacroFaces.FanFramed.framedGraph
  | .test => ColoringMacroFaces.TestFramed.framedGraph
 def rows : (s : CellShape)→RotationRows (graph s)
  | .wireTop | .wireBottom | .wireDown => ColoringMacroFaces.WireFramed.typedRows
  | .cross => ColoringMacroFaces.CrossFramed.typedRows
  | .fan => ColoringMacroFaces.FanFramed.typedRows
  | .test => ColoringMacroFaces.TestFramed.typedRows
 def leftVertex : (s : CellShape)→Fin (leftCount s)→Fin (vertexCount s)
  | .wireTop | .wireBottom | .wireDown => ColoringMacroFaces.WireFramed.leftVertex
  | .cross => ColoringMacroFaces.CrossFramed.leftVertex
  | .fan => ColoringMacroFaces.FanFramed.leftVertex
  | .test => ColoringMacroFaces.TestFramed.leftVertex
 def rightVertex : (s : CellShape)→Fin (rightCount s)→Fin (vertexCount s)
  | .wireTop | .wireBottom | .wireDown => ColoringMacroFaces.WireFramed.rightVertex
  | .cross => ColoringMacroFaces.CrossFramed.rightVertex
  | .fan => ColoringMacroFaces.FanFramed.rightVertex
  | .test => ColoringMacroFaces.TestFramed.rightVertex
 def leftClosing : (s : CellShape)→Fin (leftCount s)→Dart (Fin (edgeCount s))
  | .wireTop | .wireBottom | .wireDown => ColoringMacroFaces.WireFramed.leftClosing
  | .cross => ColoringMacroFaces.CrossFramed.leftClosing
  | .fan => ColoringMacroFaces.FanFramed.leftClosing
  | .test => ColoringMacroFaces.TestFramed.leftClosing
 def rightClosing : (s : CellShape)→Fin (rightCount s)→Dart (Fin (edgeCount s))
  | .wireTop | .wireBottom | .wireDown => ColoringMacroFaces.WireFramed.rightClosing
  | .cross => ColoringMacroFaces.CrossFramed.rightClosing
  | .fan => ColoringMacroFaces.FanFramed.rightClosing
  | .test => ColoringMacroFaces.TestFramed.rightClosing

 theorem leftCount_pos (s : CellShape) : 0<leftCount s := by cases s <;> decide
 theorem left_host (s : CellShape) (i : Fin (leftCount s)) :
    ((graph s).dartPair (leftClosing s i)).1=leftVertex s i := by
  cases s with
  | wireTop => exact ColoringMacroFaces.WireFramed.leftClosing_host i
  | wireBottom => exact ColoringMacroFaces.WireFramed.leftClosing_host i
  | wireDown => exact ColoringMacroFaces.WireFramed.leftClosing_host i
  | cross => exact ColoringMacroFaces.CrossFramed.leftClosing_host i
  | fan => exact ColoringMacroFaces.FanFramed.leftClosing_host i
  | test => exact ColoringMacroFaces.TestFramed.leftClosing_host i
 theorem right_host (s : CellShape) (i : Fin (rightCount s)) :
    ((graph s).dartPair (rightClosing s i)).1=rightVertex s i := by
  cases s with
  | wireTop => exact ColoringMacroFaces.WireFramed.rightClosing_host i
  | wireBottom => exact ColoringMacroFaces.WireFramed.rightClosing_host i
  | wireDown => exact ColoringMacroFaces.WireFramed.rightClosing_host i
  | cross => exact ColoringMacroFaces.CrossFramed.rightClosing_host i
  | fan => exact ColoringMacroFaces.FanFramed.rightClosing_host i
  | test => exact ColoringMacroFaces.TestFramed.rightClosing_host i
 theorem euler (s : CellShape) : vertexCount s+count (rows s).facePerm=edgeCount s+2 := by
  cases s with
  | wireTop => simpa only [Fintype.card_fin] using ColoringMacroFaces.WireFramed.typedRows_euler
  | wireBottom => simpa only [Fintype.card_fin] using ColoringMacroFaces.WireFramed.typedRows_euler
  | wireDown => simpa only [Fintype.card_fin] using ColoringMacroFaces.WireFramed.typedRows_euler
  | cross => simpa only [Fintype.card_fin] using ColoringMacroFaces.CrossFramed.typedRows_euler
  | fan => simpa only [Fintype.card_fin] using ColoringMacroFaces.FanFramed.typedRows_euler
  | test => simpa only [Fintype.card_fin] using ColoringMacroFaces.TestFramed.typedRows_euler
 theorem connected (s : CellShape) : ∀a b,(graph s).componentSetoid Finset.univ a b := by
  cases s with
  | wireTop => exact ColoringMacroFaces.WireFramed.framedGraph_connected
  | wireBottom => exact ColoringMacroFaces.WireFramed.framedGraph_connected
  | wireDown => exact ColoringMacroFaces.WireFramed.framedGraph_connected
  | cross => exact ColoringMacroFaces.CrossFramed.framedGraph_connected
  | fan => exact ColoringMacroFaces.FanFramed.framedGraph_connected
  | test => exact ColoringMacroFaces.TestFramed.framedGraph_connected

 def tripleChannel (i : ℕ) : Fin 3 := ⟨2-i%3,by have := Nat.mod_lt i (by omega : 0<3); omega⟩
 def leftPort : (s : CellShape)→Fin (leftCount s)→LocalPatch.Port s
  | .wireTop,i | .wireBottom,i | .wireDown,i => (⟨0,by decide⟩,tripleChannel i.val)
  | .cross,i => (⟨1-i.val/3,by change 1-i.val/3<4; omega⟩,tripleChannel i.val)
  | .fan,i => (⟨0,by decide⟩,tripleChannel i.val)
  | .test,i => (⟨i.val/3,by change i.val/3<3; have := i.isLt; change i.val<9 at this; omega⟩,tripleChannel i.val)
 def rightPort : (s : CellShape)→Fin (rightCount s)→LocalPatch.Port s
  | .wireTop,i | .wireBottom,i | .wireDown,i => (⟨1,by decide⟩,tripleChannel i.val)
  | .cross,i => (⟨2+i.val/3,by change 2+i.val/3<4; have := i.isLt; change i.val<6 at this; omega⟩,tripleChannel i.val)
  | .fan,i => (⟨2-i.val/3,by change 2-i.val/3<3; omega⟩,tripleChannel i.val)
  | .test,i => i.elim0

 def portMap (s : CellShape) : Fin (leftCount s)⊕Fin (rightCount s)→LocalPatch.Port s :=
  Sum.elim (leftPort s) (rightPort s)
 theorem portMap_bijective (s : CellShape) : Function.Bijective (portMap s) := by
  cases s <;> decide +kernel
 def portEquiv (s : CellShape) : (Fin (leftCount s)⊕Fin (rightCount s))≃LocalPatch.Port s :=
  Equiv.ofBijective (portMap s) (portMap_bijective s)
 def portClosing (s : CellShape) (p : LocalPatch.Port s) : Dart (Fin (edgeCount s)) :=
  Sum.elim (leftClosing s) (rightClosing s) ((portEquiv s).symm p)

 theorem portClosing_left (s : CellShape) (i : Fin (leftCount s)) : portClosing s (leftPort s i)=leftClosing s i := by
  change Sum.elim (leftClosing s) (rightClosing s) ((portEquiv s).symm ((portEquiv s) (.inl i)))=_
  rw [Equiv.symm_apply_apply]
  rfl
 theorem portClosing_right (s : CellShape) (i : Fin (rightCount s)) : portClosing s (rightPort s i)=rightClosing s i := by
  change Sum.elim (leftClosing s) (rightClosing s) ((portEquiv s).symm ((portEquiv s) (.inr i)))=_
  rw [Equiv.symm_apply_apply]
  rfl

end PlanarHom.ColoringEmitter.FramedMacro
