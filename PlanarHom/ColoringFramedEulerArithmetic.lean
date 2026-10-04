import PlanarHom.ColoringFramedBaseCount
import PlanarHom.ColoringFramedFrontierFold

/-! NEW scalar Euler composition for the exact canonical face program. The
vertex identity is a separate finite registry allocation equality. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem cell_sum_eq (f : NumericFormula) (w : Cell→ℕ) :
    ((canvas f).map w).sum=∑i : Canvas.Index f,w (canvasCell f i) := by
  have hh:=congrArg (fun xs : List Cell=>(xs.map w).sum) (List.ofFn_get (canvas f))
  simpa only [List.map_ofFn,List.sum_ofFn,canvasCell,Function.comp_def] using hh.symm

 theorem program_edge_card (f : NumericFormula) :
    Fintype.card (Edge f)=3*f.1+∑i : Canvas.Index f,FramedMacro.edgeCount (canvasCell f i).shape := by
  simp only [Edge,Fintype.card_sum,Fintype.card_fin,Fintype.card_sigma,PatchEdge]

 theorem euler_from_face_fold (f : NumericFormula) (hf : NumericValid f) (hn : 0<f.1) (v : ℕ)
    (hfold : count (finalFace f hf)+2*(canvas f).length=count (baseFace f)+
      ((canvas f).map (fun c=>FramedMacro.leftCount c.shape)).sum)
    (hv : v+(∑i : Canvas.Index f,FramedMacro.leftCount (canvasCell f i).shape)=
      3*f.1+(∑i : Canvas.Index f,FramedMacro.vertexCount (canvasCell f i).shape)) :
    v+count (finalFace f hf)=Fintype.card (Edge f)+2 := by
  have hb:=baseFace_count f hn
  have hl:=macro_euler_sum f
  rw [cell_sum_eq] at hfold
  rw [program_edge_card]
  omega

end PlanarHom.ColoringEmitter.FramedCanvas
