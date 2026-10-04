import PlanarHom.ColoringFramedFaceProgramCorrectness
import PlanarHom.ColoringFramedFinalFaceEuler

/-! Full Euler for the literal canonical augmented canvas rotation. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open FinitePermutationCycles ParsimoniousNorOneInThree

 theorem fullRows_euler (f : NumericFormula) (hf : NumericValid f) (hn : 0<f.1) :
    Fintype.card (Vertex f)+count (fullRows f).facePerm=Fintype.card (Edge f)+2 := by
  rw [fullRows_face_eq_finalFace f hf]
  exact finalFace_euler f hf hn

 theorem fullRows_euler_of_nonempty (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) :
    Fintype.card (Vertex f)+count (fullRows f).facePerm=Fintype.card (Edge f)+2 := by
  rw [fullRows_face_eq_finalFace f hf]
  exact finalFace_euler_of_nonempty f hf hne

end PlanarHom.ColoringEmitter.FramedCanvas
