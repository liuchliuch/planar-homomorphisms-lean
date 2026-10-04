import PlanarHom.ColoringFramedFrontierFold
import PlanarHom.ColoringFramedFutureSupport

/-! NEW unconditional support instantiation for the actual cell sequence.
Every future macro is proved untouched and separated from each earlier input
producer directly from the canonical registry allocation. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem cell_step (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f)
    (i : Canvas.Index f) (pre post : List PortData)
    (hfront : CyclicSublist (prefixFace f hf i.val)
      (frontierWord f hf fallback (pre++(canvasCell f i).leftFrontier++post))) :
    count (prefixFace f hf (i.val+1))+2=count (prefixFace f hf i.val)+sharedCount f i ∧
      CyclicSublist (prefixFace f hf (i.val+1))
        (frontierWord f hf fallback (pre++(canvasCell f i).rightFrontier++post)) :=
  cell_step_of_support f hf fallback i pre post
    (prefixFace_patch_future f hf i.val i (le_refl _)) (prefixFace_old_new_not_sameCycle f hf i) hfront

 theorem frontierRun_fold (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f)
    {xs ys : List PortData} {cs : List Cell} (hrun : FrontierRun xs cs ys)
    (k : ℕ) (hcs : cs=(canvas f).drop k)
    (hfront : CyclicSublist (prefixFace f hf k) (frontierWord f hf fallback xs)) :
    count (prefixFace f hf (k+cs.length))+2*cs.length=
      count (prefixFace f hf k)+(cs.map (fun c=>FramedMacro.leftCount c.shape)).sum ∧
    CyclicSublist (prefixFace f hf (k+cs.length)) (frontierWord f hf fallback ys) :=
  frontierRun_fold_of_support f hf fallback
    (fun i=>prefixFace_patch_future f hf i.val i (le_refl _))
    (prefixFace_old_new_not_sameCycle f hf) hrun k hcs hfront

 theorem canvas_face_fold (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f)
    (hinitial : CyclicSublist (baseFace f) (frontierWord f hf fallback (railFrontier 0 0 (List.range f.1)))) :
    count (finalFace f hf)+2*(canvas f).length=count (baseFace f)+
      ((canvas f).map (fun c=>FramedMacro.leftCount c.shape)).sum :=
  canvas_face_fold_of_support f hf fallback
    (fun i=>prefixFace_patch_future f hf i.val i (le_refl _))
    (prefixFace_old_new_not_sameCycle f hf) hinitial

end PlanarHom.ColoringEmitter.FramedCanvas
