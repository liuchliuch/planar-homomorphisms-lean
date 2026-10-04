import PlanarHom.ColoringFramedCellStep
import PlanarHom.ColoringCanvasFrontierComplete

/-! NEW complete induction over the literal emitted cell trace. The actual
face program and actual named frontiers are used at every step. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem frontierRun_fold_of_support (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f)
    (hsupport : ∀i : Canvas.Index f,∀a,prefixFace f hf i.val (patchDart f i a)=
      patchDart f i ((FramedMacro.rows (canvasCell f i).shape).facePerm a))
    (hseparate : ∀i : Canvas.Index f,¬(prefixFace f hf i.val).SameCycle (oldMarker f hf i 0) (newMarker f i 0))
    {xs ys : List PortData} {cs : List Cell} (hrun : FrontierRun xs cs ys)
    (k : ℕ) (hcs : cs=(canvas f).drop k)
    (hfront : CyclicSublist (prefixFace f hf k) (frontierWord f hf fallback xs)) :
    count (prefixFace f hf (k+cs.length))+2*cs.length=
      count (prefixFace f hf k)+(cs.map (fun c=>FramedMacro.leftCount c.shape)).sum ∧
    CyclicSublist (prefixFace f hf (k+cs.length)) (frontierWord f hf fallback ys) := by
  induction hrun generalizing k with
  | nil xs =>
      simp only [List.length_nil,List.map_nil,List.sum_nil,Nat.add_zero,Nat.mul_zero]
      exact ⟨trivial,hfront⟩
  | cons pre post c cs ys htail ih =>
      have hk : k<(canvas f).length := by
        by_contra hh
        have hz : (canvas f).drop k=[] := List.drop_eq_nil_iff.mpr (by omega)
        rw [hz] at hcs
        cases hcs
      let i : Canvas.Index f := ⟨k,hk⟩
      have he : c::cs=(canvas f)[k]::(canvas f).drop (k+1) := hcs.trans (List.drop_eq_getElem_cons hk)
      have hc : c=canvasCell f i := (List.cons.inj he).1
      have hcs' : cs=(canvas f).drop (k+1) := (List.cons.inj he).2
      have hstep:=cell_step_of_support f hf fallback i pre post (hsupport i) (hseparate i)
        (by simpa only [hc] using hfront)
      have htail':=ih (k+1) hcs' (by simpa only [hc] using hstep.2)
      simp only [List.length_cons,List.map_cons,List.sum_cons]
      rw [show k+(cs.length+1)=(k+1)+cs.length by omega]
      constructor
      · have hs:=hstep.1
        change count (prefixFace f hf (k+1))+2=count (prefixFace f hf k)+FramedMacro.leftCount (canvasCell f i).shape at hs
        rw [←hc] at hs
        have ht:=htail'.1
        omega
      · exact htail'.2

 theorem canvas_face_fold_of_support (f : NumericFormula) (hf : NumericValid f) (fallback : Boundary f)
    (hsupport : ∀i : Canvas.Index f,∀a,prefixFace f hf i.val (patchDart f i a)=
      patchDart f i ((FramedMacro.rows (canvasCell f i).shape).facePerm a))
    (hseparate : ∀i : Canvas.Index f,¬(prefixFace f hf i.val).SameCycle (oldMarker f hf i 0) (newMarker f i 0))
    (hinitial : CyclicSublist (baseFace f) (frontierWord f hf fallback (railFrontier 0 0 (List.range f.1)))) :
    count (finalFace f hf)+2*(canvas f).length=count (baseFace f)+
      ((canvas f).map (fun c=>FramedMacro.leftCount c.shape)).sum := by
  have hh:=frontierRun_fold_of_support f hf fallback hsupport hseparate (canvas_frontierRun f hf) 0 rfl hinitial
  simpa only [Nat.zero_add,prefixFace,finalFace] using hh.1

end PlanarHom.ColoringEmitter.FramedCanvas
