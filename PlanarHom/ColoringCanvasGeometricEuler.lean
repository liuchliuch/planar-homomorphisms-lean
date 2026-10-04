import PlanarHom.ColoringFramedRowsEuler
import PlanarHom.ColoringFramedCanvasConnected
import PlanarHom.ColoringFramedSourceRotation
import PlanarHom.ColoringFramedSelectedFlip
import PlanarHom.ColoringFramedRetainedCardinality
import PlanarHom.ColoringCanvasNoIsolates
import PlanarHom.RotationRowsHereditaryEuler

/-! Euler for the actual original coloring canvas rotation. Auxiliary seed and
frame edges are removed using hereditary Euler and the exact finite marker
count balance; all isolated frame corners are counted and cancelled explicitly. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree RadialPotts.Assembly

 theorem selected_choice (f : NumericFormula) :
    (fun e=>decide (e∈selectedEdges f))=keepEdge f := by
  funext e
  simp only [selectedEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  exact Bool.decide_coe (keepEdge f e)

 theorem selected_fullRows_euler (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) :
    Fintype.card (Vertex f)+count ((fullRows f).rotation*selectedFlip (keepEdge f))=
      Fintype.card (Canvas.Edge f)+2*((Canvas.graph f).componentCount Finset.univ+Fintype.card (Corner f)) := by
  have hn := positive_inputs_of_formula_nonempty f hf hne
  have he : Fintype.card (Vertex f)+count (fullRows f).facePerm=
      Fintype.card (Edge f)+2*(graph f).componentCount Finset.univ := by
    rw [graph_componentCount f hf hn,Nat.mul_one]
    exact fullRows_euler_of_nonempty f hf hne
  have hs := RotationRows.hereditary_euler (fullRows f) (graph_incident f hf hn) he (selectedEdges f)
  rw [selectedEdges_card,selected_componentCount] at hs
  simpa only [selectedEdges,Finset.mem_filter,Finset.mem_univ,true_and,Bool.decide_coe] using hs

 theorem selected_face_marker_balance (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) :
    count ((fullRows f).rotation*selectedFlip (keepEdge f))+Fintype.card (Canvas.Vertex f)=
      count (Canvas.geometricRows f).facePerm+Fintype.card (Vertex f) := by
  let R := (dartPartition f).permCongr (fullRows f).rotation
  have hb := eraseFinMarkers_count_balance (markerCount f) R (reversePerm (Canvas.Edge f))
  have hr : count R=Fintype.card (Vertex f) := by
    rw [show count R=count (fullRows f).rotation from count_permCongr _ (dartPartition f)]
    exact RotationRows.rotation_count_of_incident (fullRows f)
      (graph_incident f hf (positive_inputs_of_formula_nonempty f hf hne))
  have he : eraseFinMarkers R=(Canvas.geometricRows f).rotation := erase_fullRows_rotation f
  have hs : count (Canvas.geometricRows f).rotation=Fintype.card (Canvas.Vertex f) :=
    RotationRows.rotation_count_of_incident (Canvas.geometricRows f) (Canvas.dart_host_surjective f hf hne)
  have hp : count (R*Equiv.sumCongr (reversePerm (Canvas.Edge f)) (Equiv.refl (Fin (markerCount f))))=
      count ((fullRows f).rotation*selectedFlip (keepEdge f)) := by
    dsimp only [R]
    rw [←partition_selectedFlip f,←permCongr_mul]
    exact count_permCongr _ (dartPartition f)
  rw [hp,he,hs,hr] at hb
  exact hb

end PlanarHom.ColoringEmitter.FramedCanvas
namespace PlanarHom.ColoringEmitter.Canvas
open FinitePermutationCycles ParsimoniousNorOneInThree

 theorem geometricRows_euler (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) :
    Fintype.card (Vertex f)+count (geometricRows f).facePerm=
      Fintype.card (Edge f)+2*(graph f).componentCount Finset.univ := by
  have hs := FramedCanvas.selected_fullRows_euler f hf hne
  have hb := FramedCanvas.selected_face_marker_balance f hf hne
  have hv := FramedCanvas.vertex_card_split f
  omega

end PlanarHom.ColoringEmitter.Canvas
