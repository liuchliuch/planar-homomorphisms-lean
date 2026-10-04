import PlanarHom.ColoringFramedCellCorrectness
import PlanarHom.ColoringFramedInitialFrontier
import PlanarHom.ColoringFramedEmptyInput
import PlanarHom.ColoringFramedEulerArithmetic
import PlanarHom.ColoringFramedCanvasCardinality

/-! NEW complete original-input Euler proof for the literal global framed
face-splice program. The emitted routing trace, registry, seed, and all macro
face words are supplied by the preceding constructive proofs. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem finalFace_count_fold (f : NumericFormula) (hf : NumericValid f) :
    count (finalFace f hf)+2*(canvas f).length=count (baseFace f)+
      ((canvas f).map (fun c=>FramedMacro.leftCount c.shape)).sum := by
  by_cases hn : 0<f.1
  · let fallback : Boundary f := initialBoundary f ⟨0,hn⟩
    exact canvas_face_fold f hf fallback (initial_frontier_cyclic f hf fallback hn)
  · exact face_fold_zero f hf (by omega)

 theorem finalFace_euler (f : NumericFormula) (hf : NumericValid f) (hn : 0<f.1) :
    Fintype.card (Vertex f)+count (finalFace f hf)=Fintype.card (Edge f)+2 :=
  euler_from_face_fold f hf hn (Fintype.card (Vertex f)) (finalFace_count_fold f hf) (vertex_card_balance f hf)

 theorem finalFace_euler_of_nonempty (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) :
    Fintype.card (Vertex f)+count (finalFace f hf)=Fintype.card (Edge f)+2 :=
  finalFace_euler f hf (positive_inputs_of_formula_nonempty f hf hne)

end PlanarHom.ColoringEmitter.FramedCanvas
