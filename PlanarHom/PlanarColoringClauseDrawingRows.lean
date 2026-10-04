import PlanarHom.PlanarColoringClauseCoordinates
noncomputable section
namespace PlanarHom.PlanarColoringClause
set_option maxHeartbeats 5000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000

def DrawingRow (e : Edge) : Prop :=
  (∀ f : Edge,e≠f → IntegerStraightDrawing.Separated
    (integerPoint (graph.src e)) (integerPoint (graph.dst e))
    (integerPoint (graph.src f)) (integerPoint (graph.dst f))) ∧
  (∀ v : Vertex,IntegerStraightDrawing.Avoids
    (integerPoint (graph.src e)) (integerPoint (graph.dst e)) (integerPoint v)) ∧
  integerPoint (graph.src e)≠integerPoint (graph.dst e)
end PlanarHom.PlanarColoringClause
