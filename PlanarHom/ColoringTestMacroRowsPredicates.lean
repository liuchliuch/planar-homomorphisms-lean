import PlanarHom.ColoringTestMacroRows
import PlanarHom.GeometricRowCertificate
noncomputable section
namespace PlanarHom.ColoringTestMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
 def VertexGood (v : Vertex) : Prop := (row v).Nodup ∧ (row v).all (fun a=>decide ((graph.dartPair a).1=v))=true
 instance (v : Vertex) : Decidable (VertexGood v) := inferInstanceAs (Decidable (_ ∧ _))
 def DartGood (e : Edge) : Prop := ∀b : Bool,(row (graph.dartPair (e,b)).1)[position (e,b)]?=some (e,b)
 instance (e : Edge) : Decidable (DartGood e) := inferInstanceAs (Decidable (∀b : Bool,_))
end PlanarHom.ColoringTestMacroRows
