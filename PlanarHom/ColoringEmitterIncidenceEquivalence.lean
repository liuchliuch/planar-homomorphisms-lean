import PlanarHom.ColoringEmitterLocalVertexTranslation
import PlanarHom.ColoringEmitterEdgeEquivalence

/-! NEW exact global typed/numeric incidence bijection. Every original macro
edge occurrence retains its literal position in the emitted concatenation. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph PositiveBlockProgram ParsimoniousNorOneInThree Complexity

 theorem state_valid (f : NumericFormula) : (graphOf (state f)).Valid 1 0 :=
   graphOf_valid _ (run_valid _ _)

 def state_incidenceEquiv (f : NumericFormula) (hf:NumericValid f) :
     IncidenceEquiv (graph f) ((graphOf (state f)).toMultiGraph (state_valid f)) where
   vertex := vertexEquiv f hf
   edge := edgeEquiv f
   src_eq e := by
     rcases e with ⟨i,e⟩
     apply Fin.ext
     change ((state f).edges.get (edgeEquiv f ⟨i,e⟩)).1=
       (vertexEquiv f hf (PortPatchAssembly.placeVertex (port f) i ((patch f i).src e))).val
     rw [state_edge_get,vertex_local]
     simp only [patch,LocalPatch.graph_source,LocalPatch.numericGraph]
   dst_eq e := by
     rcases e with ⟨i,e⟩
     apply Fin.ext
     change ((state f).edges.get (edgeEquiv f ⟨i,e⟩)).2.1=
       (vertexEquiv f hf (PortPatchAssembly.placeVertex (port f) i ((patch f i).dst e))).val
     rw [state_edge_get,vertex_local]
     simp only [patch,LocalPatch.graph_target,LocalPatch.numericGraph]

 theorem compile_eq_state (f : NumericFormula) (hne:f.2≠[]) : compile f=graphOf (state f) := by
   simp only [compile,if_neg hne,state]

 def codeIncidenceEquiv (g h : MixedCode) (hg:g.Valid 1 0) (hh:h.Valid 1 0)
     (he:g=h) : IncidenceEquiv (g.toMultiGraph hg) (h.toMultiGraph hh) := by
   subst h
   exact ⟨Equiv.refl _,Equiv.refl _,fun _=>rfl,fun _=>rfl⟩

 /-- The empty formula has its own literal empty-graph compiler branch. -/
 def compile_incidenceEquiv (f : NumericFormula) (hf:NumericValid f) (hne:f.2≠[]) :
     IncidenceEquiv (graph f) ((compile f).toMultiGraph (compile_valid f)) :=
   (state_incidenceEquiv f hf).trans
     (codeIncidenceEquiv (graphOf (state f)) (compile f) (state_valid f)
       (compile_valid f) (compile_eq_state f hne).symm)

end PlanarHom.ColoringEmitter.Canvas
