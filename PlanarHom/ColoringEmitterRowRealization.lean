import PlanarHom.ColoringEmitterRowTransport
import PlanarHom.ColoringEmitterIncidenceDarts

/-! NEW transport from the literal emitted row table to its actual numeric
incidence graph, including the exact row list at every numeric vertex. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree PlanarityLRRealization
open ColoringEmitterRows

 theorem rows_getD_eq (f : NumericFormula) (hf:NumericValid f) (hne:f.2≠[])
     (rs : ∀i,RotationRows (patch f i)) (table : RowTable) (hrow:LocalRowLaw f rs table)
     (v : Fin (compile f).vertices) :
     (ColoringEmitterRows.rows table f).getD v.val []=
       (((rowsFrom f rs).transport (compile_incidenceEquiv f hf hne)).row v).map eraseDart := by
   obtain ⟨w,rfl⟩:=(compile_incidenceEquiv f hf hne).vertex.surjective v
   simp only [ColoringEmitterRows.rows,List.getD_eq_getElem?_getD,List.getElem?_map,
     List.getElem?_range ((compile_incidenceEquiv f hf hne).vertex w).isLt,Option.map_some,Option.getD_some]
   rw [compile_vertex_val,programRow_eq f hf rs table hrow]
   simp only [RotationRows.transport,Equiv.symm_apply_apply,List.map_map]
   apply List.map_congr_left
   intro a _
   change ((edgeEquiv f a.1).val,a.2)=(((compile_incidenceEquiv f hf hne).edge a.1).val,a.2)
   rw [compile_edge_val]

end PlanarHom.ColoringEmitter.Canvas
