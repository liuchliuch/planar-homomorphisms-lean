import PlanarHom.ColoringEmitterIncidenceEquivalence
import PlanarHom.RotationRowsTransport

noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph Complexity PositiveBlockProgram ParsimoniousNorOneInThree

 theorem codeIncidenceEquiv_vertex_val (g h : MixedCode) (hg:g.Valid 1 0) (hh:h.Valid 1 0)
     (he:g=h) (v : Fin g.vertices) :
     ((codeIncidenceEquiv g h hg hh he).vertex v).val=v.val := by subst h; rfl

 theorem codeIncidenceEquiv_edge_val (g h : MixedCode) (hg:g.Valid 1 0) (hh:h.Valid 1 0)
     (he:g=h) (e : Fin g.edges.length) :
     ((codeIncidenceEquiv g h hg hh he).edge e).val=e.val := by subst h; rfl

 theorem compile_vertex_val (f : NumericFormula) (hf:NumericValid f) (hne:f.2≠[]) (v : Vertex f) :
     ((compile_incidenceEquiv f hf hne).vertex v).val=(vertexEquiv f hf v).val := by
   unfold compile_incidenceEquiv IncidenceEquiv.trans
   simp only [Equiv.trans_apply,codeIncidenceEquiv_vertex_val]
   rfl

 theorem compile_edge_val (f : NumericFormula) (hf:NumericValid f) (hne:f.2≠[]) (e : Edge f) :
     ((compile_incidenceEquiv f hf hne).edge e).val=(edgeEquiv f e).val := by
   unfold compile_incidenceEquiv IncidenceEquiv.trans
   simp only [Equiv.trans_apply,codeIncidenceEquiv_edge_val]
   rfl
end PlanarHom.ColoringEmitter.Canvas
