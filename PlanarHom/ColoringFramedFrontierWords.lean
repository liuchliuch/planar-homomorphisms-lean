import PlanarHom.ColoringFramedSpliceProgram
import PlanarHom.ColoringFramedPortWords

/-! NEW identification of actual source frontier names with the literal
producer and current-patch marker words used by the face-splice program. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 def signalForName (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f) (name : ℕ) : Boundary f :=
  if h : ∃b : Boundary f,boundaryName f hf b=name then Classical.choose h else fallback

 theorem signalForName_eq (f : NumericFormula) (hf : NumericValid f) (fallback b : Boundary f) :
    signalForName f hf fallback (boundaryName f hf b)=b := by
  have he : ∃c : Boundary f,boundaryName f hf c=boundaryName f hf b := ⟨b,rfl⟩
  rw [signalForName,dif_pos he]
  exact boundaryName_injective f hf (Classical.choose_spec he)

 def tripleWord (f : NumericFormula) (hf : NumericValid f) (b : Boundary f) : List (Dart f) :=
  [producerMarker f hf (b,2),producerMarker f hf (b,1),producerMarker f hf (b,0)]
 def frontierWord (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f) (xs : List PortData) : List (Dart f) :=
  xs.flatMap (fun p=>tripleWord f hf (signalForName f hf fallback p.1))

@[simp] theorem frontierWord_append (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f)
    (xs ys : List PortData) : frontierWord f hf fallback (xs++ys)=frontierWord f hf fallback xs++frontierWord f hf fallback ys :=
  List.flatMap_append

 theorem signalForName_port (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f)
    (i : Canvas.Index f) (p : Fin (canvasCell f i).shape.portCount) :
    signalForName f hf fallback ((canvasCell f i).portData p).1=boundaryPort f i p := by
  rw [←boundaryName_port f hf i p,signalForName_eq]

 theorem producerMarker_output (f : NumericFormula) (hf : NumericValid f) (i : Canvas.Index f)
    (o : Fin (canvasCell f i).shape.outputCount) (b : Fin 3) :
    producerMarker f hf (Canvas.port f i ((canvasCell f i).freshPort o,b))=
      patchDart f i (reversePerm _ (FramedMacro.portClosing (canvasCell f i).shape ((canvasCell f i).freshPort o,b))) := by
  have he : (Canvas.signalEquiv f hf).symm (boundaryPort f i ((canvasCell f i).freshPort o))=.inr ⟨i,o⟩ := by
    rw [←Canvas.signalEquiv_output f hf i o,Equiv.symm_apply_apply]
  simp only [producerMarker,Canvas.port,he]

 theorem left_frontier_word (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f)
    (i : Canvas.Index f) :
    frontierWord f hf fallback (canvasCell f i).leftFrontier=
      List.ofFn (fun j : Fin (sharedCount f i)=>producerMarker f hf
        (Canvas.port f i (FramedMacro.leftPort (canvasCell f i).shape j))) := by
  have hw:=congrArg (fun ps : List (LocalPatch.Port (canvasCell f i).shape)=>
    ps.map (fun p=>producerMarker f hf (Canvas.port f i p))) (FramedMacro.leftPort_word (canvasCell f i).shape)
  simp only [List.map_ofFn,Function.comp_def] at hw
  refine Eq.trans ?_ hw.symm
  simp only [frontierWord,Cell.leftFrontier,List.flatMap_map,List.map_flatMap,List.map_cons,List.map_nil]
  congr 1
  funext p
  simp only [tripleWord,signalForName_port,Canvas.port,Function.comp_apply]

 theorem oldMarker_word (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f)
    (i : Canvas.Index f) : List.ofFn (oldMarker f hf i)=frontierWord f hf fallback (canvasCell f i).leftFrontier := by
  rw [left_frontier_word]
  apply List.ext_getElem
  · simp only [List.length_ofFn,sharedPred_succ]
  · intro j hj hk
    simp only [List.getElem_ofFn,oldMarker,sharedIndex,finCongr_apply]
    apply congrArg (fun z : Fin (sharedCount f i)=>producerMarker f hf (Canvas.port f i (FramedMacro.leftPort (canvasCell f i).shape z)))
    exact Fin.ext rfl

 theorem right_frontier_word (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f)
    (i : Canvas.Index f) : frontierWord f hf fallback (canvasCell f i).rightFrontier=
      List.ofFn (fun j : Fin (FramedMacro.rightCount (canvasCell f i).shape)=>
        patchDart f i (reversePerm _ (FramedMacro.rightClosing (canvasCell f i).shape j))) := by
  have hw : frontierWord f hf fallback (canvasCell f i).rightFrontier=
      List.ofFn (fun j : Fin (FramedMacro.rightCount (canvasCell f i).shape)=>
        producerMarker f hf (Canvas.port f i (FramedMacro.rightPort (canvasCell f i).shape j))) := by
    have hh:=congrArg (fun ps : List (LocalPatch.Port (canvasCell f i).shape)=>
      ps.map (fun p=>producerMarker f hf (Canvas.port f i p))) (FramedMacro.rightPort_word (canvasCell f i).shape)
    simp only [List.map_ofFn,Function.comp_def] at hh
    refine Eq.trans ?_ hh.symm
    simp only [frontierWord,Cell.rightFrontier,List.flatMap_map,List.map_flatMap,List.map_cons,List.map_nil]
    congr 1
    funext p
    simp only [tripleWord,signalForName_port,Canvas.port,Function.comp_apply]
  rw [hw]
  apply congrArg List.ofFn
  funext j
  have hp:=FramedMacro.rightPort_fresh (canvasCell f i) j
  have hpair : FramedMacro.rightPort (canvasCell f i).shape j=
      ((canvasCell f i).freshPort (FramedMacro.rightOutput (canvasCell f i).shape j),
        (FramedMacro.rightPort (canvasCell f i).shape j).2) := Prod.ext hp rfl
  rw [hpair,producerMarker_output,←hpair,FramedMacro.portClosing_right]

 theorem newMarker_word (f : NumericFormula) (i : Canvas.Index f) : List.ofFn (newMarker f i)=
    (List.ofFn (fun j : Fin (sharedCount f i)=>reversePerm _ (FramedMacro.leftClosing (canvasCell f i).shape j))).map (patchDart f i) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,sharedPred_succ]
  · intro j hj hk
    simp only [List.getElem_ofFn,List.getElem_map,newMarker,sharedIndex,finCongr_apply]
    apply congrArg (fun z : Fin (sharedCount f i)=>patchDart f i (reversePerm _ (FramedMacro.leftClosing (canvasCell f i).shape z)))
    exact Fin.ext rfl

 theorem patchDart_isEmbedding (f : NumericFormula) (i : Canvas.Index f) : Function.Injective (patchDart f i) := by
  rintro ⟨e,b⟩ ⟨e',b'⟩ h
  have hh:=congrArg Prod.fst h
  have hb:=congrArg Prod.snd h
  have he : e=e' := by simpa only [patchDart,Sum.inr.injEq,Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh
  exact Prod.ext he hb

end PlanarHom.ColoringEmitter.FramedCanvas
