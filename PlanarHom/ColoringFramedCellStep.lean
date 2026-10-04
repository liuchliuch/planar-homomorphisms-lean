import PlanarHom.ColoringFramedFrontierWords
import PlanarHom.ColoringFramedMacroCyclic
import PlanarHom.FinitePermutationFrontierStep

/-! NEW actual cell step of the canonical framed face program. The source
frontier names are identified with literal registry-origin marker arrays. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem cell_step_of_support (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f)
    (i : Canvas.Index f) (pre post : List PortData)
    (hfuture : ∀a,prefixFace f hf i.val (patchDart f i a)=
      patchDart f i ((FramedMacro.rows (canvasCell f i).shape).facePerm a))
    (hsep : ¬(prefixFace f hf i.val).SameCycle (oldMarker f hf i 0) (newMarker f i 0))
    (hfront : CyclicSublist (prefixFace f hf i.val)
      (frontierWord f hf fallback (pre++(canvasCell f i).leftFrontier++post))) :
    count (prefixFace f hf (i.val+1))+2=count (prefixFace f hf i.val)+sharedCount f i ∧
      CyclicSublist (prefixFace f hf (i.val+1))
        (frontierWord f hf fallback (pre++(canvasCell f i).rightFrontier++post)) := by
  have hold : CyclicSublist (prefixFace f hf i.val)
      (frontierWord f hf fallback pre++List.ofFn (oldMarker f hf i)++frontierWord f hf fallback post) := by
    rw [oldMarker_word f hf fallback i]
    simpa only [frontierWord_append] using hfront
  have hnew : CyclicSublist (prefixFace f hf i.val)
      ((List.ofFn (newMarker f i)).reverse++frontierWord f hf fallback (canvasCell f i).rightFrontier) := by
    have hh:=CyclicSublist.map_embedding (FramedMacro.rows (canvasCell f i).shape).facePerm
      (prefixFace f hf i.val) (patchDart f i) (patchDart_isEmbedding f i) hfuture
      (FramedMacro.ports_cyclic (canvasCell f i).shape)
    simpa only [List.map_append,List.map_reverse,List.map_ofFn,newMarker_word,right_frontier_word] using hh
  have hh:=splicePrefix_frontier_step (prefixFace f hf i.val) (sharedPred f i)
    (oldMarker f hf i) (newMarker f i) (frontierWord f hf fallback pre)
    (frontierWord f hf fallback post) (frontierWord f hf fallback (canvasCell f i).rightFrontier)
    hold hnew hsep
  rw [prefixFace_step]
  constructor
  · have hs:=sharedPred_succ f i
    have hcount:=hh.1
    change count (spliceCell f hf (prefixFace f hf i.val) i)+1=count (prefixFace f hf i.val)+sharedPred f i at hcount
    omega
  · simpa only [frontierWord_append,List.append_assoc] using hh.2

end PlanarHom.ColoringEmitter.FramedCanvas
