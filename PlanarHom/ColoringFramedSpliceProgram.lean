import PlanarHom.ColoringFramedMacroFamily
import PlanarHom.ColoringCanvasInputFreshness
import PlanarHom.FinitePermutationBoundaryPathSplice
import PlanarHom.FinitePermutationBoundaryPathWord
import Mathlib.GroupTheory.Perm.Fin

/-! NEW literal face-splice program on the canonical occurrence carrier.
Every input pair is named by its actual original/earlier-output registry origin;
no embedding, Euler, cofaciality, or frontier-order data enter the program. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

abbrev PatchEdge (f : NumericFormula) (i : Canvas.Index f) := Fin (FramedMacro.edgeCount (canvasCell f i).shape)
abbrev Edge (f : NumericFormula) := Fin (3*f.1) ⊕ Sigma (PatchEdge f)
abbrev Dart (f : NumericFormula) := MultiGraph.Kasteleyn.Dart (Edge f)

 def seedFace (N : ℕ) : Equiv.Perm (MultiGraph.Kasteleyn.Dart (Fin N)) where
  toFun a:=if a.2 then (finRotate N a.1,true) else ((finRotate N).symm a.1,false)
  invFun a:=if a.2 then ((finRotate N).symm a.1,true) else (finRotate N a.1,false)
  left_inv a:=by rcases a with ⟨a,b⟩; cases b <;> simp
  right_inv a:=by rcases a with ⟨a,b⟩; cases b <;> simp

 def seedDart (f : NumericFormula) (a : MultiGraph.Kasteleyn.Dart (Fin (3*f.1))) : Dart f := (.inl a.1,a.2)
 def patchDart (f : NumericFormula) (i : Canvas.Index f) (a : MultiGraph.Kasteleyn.Dart (PatchEdge f i)) : Dart f := (.inr ⟨i,a.1⟩,a.2)

 def baseFace (f : NumericFormula) : Equiv.Perm (Dart f) where
  toFun
    | (.inl e,b) => seedDart f (seedFace (3*f.1) (e,b))
    | (.inr ⟨i,e⟩,b) => patchDart f i ((FramedMacro.rows (canvasCell f i).shape).facePerm (e,b))
  invFun
    | (.inl e,b) => seedDart f ((seedFace (3*f.1)).symm (e,b))
    | (.inr ⟨i,e⟩,b) => patchDart f i ((FramedMacro.rows (canvasCell f i).shape).facePerm.symm (e,b))
  left_inv a:=by
    rcases a with ⟨e|⟨i,e⟩,b⟩
    · change seedDart f ((seedFace (3*f.1)).symm (seedFace (3*f.1) (e,b)))=seedDart f (e,b)
      rw [Equiv.symm_apply_apply]
    · change patchDart f i ((FramedMacro.rows (canvasCell f i).shape).facePerm.symm
        ((FramedMacro.rows (canvasCell f i).shape).facePerm (e,b)))=patchDart f i (e,b)
      rw [Equiv.symm_apply_apply]
  right_inv a:=by
    rcases a with ⟨e|⟨i,e⟩,b⟩
    · change seedDart f (seedFace (3*f.1) ((seedFace (3*f.1)).symm (e,b)))=seedDart f (e,b)
      rw [Equiv.apply_symm_apply]
    · change patchDart f i ((FramedMacro.rows (canvasCell f i).shape).facePerm
        ((FramedMacro.rows (canvasCell f i).shape).facePerm.symm (e,b)))=patchDart f i (e,b)
      rw [Equiv.apply_symm_apply]

 def initialVertex (f : NumericFormula) (i : Fin f.1) (channel : Fin 3) : Fin (3*f.1) :=
  ⟨3*i.val+(2-channel.val),by have hi:=i.isLt; have hc:=channel.isLt; omega⟩

 def producerMarker (f : NumericFormula) (hf : NumericValid f) (b : Canvas.BoundaryTriple f) : Dart f :=
  match (Canvas.signalEquiv f hf).symm b.1 with
  | .inl i => seedDart f ((finRotate (3*f.1)).symm (initialVertex f i b.2),true)
  | .inr ⟨i,o⟩ => patchDart f i (reversePerm _
      (FramedMacro.portClosing (canvasCell f i).shape ((canvasCell f i).freshPort o,b.2)))

 def sharedCount (f : NumericFormula) (i : Canvas.Index f) : ℕ := FramedMacro.leftCount (canvasCell f i).shape
 def sharedPred (f : NumericFormula) (i : Canvas.Index f) : ℕ := sharedCount f i-1
 theorem sharedPred_succ (f : NumericFormula) (i : Canvas.Index f) : sharedPred f i+1=sharedCount f i := by
  have hh:=FramedMacro.leftCount_pos (canvasCell f i).shape
  change sharedCount f i>0 at hh
  unfold sharedPred
  omega
 def sharedIndex (f : NumericFormula) (i : Canvas.Index f) : Fin (sharedPred f i+1)≃Fin (sharedCount f i) :=
  finCongr (sharedPred_succ f i)

 def oldMarker (f : NumericFormula) (hf : NumericValid f) (i : Canvas.Index f) (j : Fin (sharedPred f i+1)) : Dart f :=
  producerMarker f hf (Canvas.port f i (FramedMacro.leftPort (canvasCell f i).shape (sharedIndex f i j)))
 def newMarker (f : NumericFormula) (i : Canvas.Index f) (j : Fin (sharedPred f i+1)) : Dart f :=
  patchDart f i (reversePerm _ (FramedMacro.leftClosing (canvasCell f i).shape (sharedIndex f i j)))

 def spliceCell (f : NumericFormula) (hf : NumericValid f) (P : Equiv.Perm (Dart f)) (i : Canvas.Index f) : Equiv.Perm (Dart f) :=
  splicePrefix P (extendBoundaryPath (sharedPred f i) (oldMarker f hf i))
    (extendBoundaryPath (sharedPred f i) (newMarker f i)) (sharedPred f i+1)

 def prefixFace (f : NumericFormula) (hf : NumericValid f) : ℕ→Equiv.Perm (Dart f)
  | 0 => baseFace f
  | k+1 => if hk : k<(canvas f).length then spliceCell f hf (prefixFace f hf k) ⟨k,hk⟩ else prefixFace f hf k

 def finalFace (f : NumericFormula) (hf : NumericValid f) : Equiv.Perm (Dart f) :=
  prefixFace f hf (canvas f).length

 theorem prefixFace_step (f : NumericFormula) (hf : NumericValid f) (i : Canvas.Index f) :
    prefixFace f hf (i.val+1)=spliceCell f hf (prefixFace f hf i.val) i := by
  simp only [prefixFace,dif_pos i.isLt,Fin.eta]

end PlanarHom.ColoringEmitter.FramedCanvas
