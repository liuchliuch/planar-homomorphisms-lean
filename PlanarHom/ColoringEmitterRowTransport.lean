import PlanarHom.ColoringEmitterIncidenceEquivalence
import PlanarHom.ColoringEmitterEdgeOffsets
import PlanarHom.ColoringCanvasRotationRows
import PlanarHom.ColoringEmitterRowTables
import PlanarHom.RotationRowsTransport

/-! NEW exact equality between the executable row lists and the reverse-cell
concatenation of the same local geometric rows. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree PlanarityLRRealization
open ColoringEmitterRows

 def eraseStateDart (f : NumericFormula) (a : MultiGraph.Kasteleyn.Dart (Edge f)) : ColoringEmitterRows.Dart :=
   ((edgeEquiv f a.1).val,a.2)

 def LocalRowLaw (f : NumericFormula) (rs : ∀i,RotationRows (patch f i)) (table : RowTable) : Prop :=
   ∀(i : Index f) (w : LocalPatch.NumericVertex (canvasCell f i).shape),
     ((rs i).row ((LocalPatch.localVertexParts _).symm w)).map (fun a=>(a.1.val,a.2))=
       (table (canvasCell f i).shape.kind)[w.val]?.getD []

 theorem cellRow_eq (f : NumericFormula) (hf:NumericValid f)
     (rs : ∀i,RotationRows (patch f i)) (table : RowTable) (hrow:LocalRowLaw f rs table)
     (i : Index f) (v : Vertex f) :
     cellRow table (before f i) (canvasCell f i).instruction (vertexEquiv f hf v).val=
       ((PortPatchAssembly.localRowWord (patch f) (port f) rs (localVertices f) i v).map
         (PortPatchAssembly.liftPatchDart i)).map (eraseStateDart f) := by
   unfold cellRow PortPatchAssembly.localRowWord localVertices
   rw [←List.map_coe_finRange]
   simp only [List.flatMap_map,List.map_flatMap,List.map_map]
   apply List.flatMap_congr
   intro w _
   have he : localVertex (canvasCell f i).instruction (before f i).dictionary (before f i).vertices w.val=
       (vertexEquiv f hf v).val ↔
       PortPatchAssembly.placeVertex (port f) i ((LocalPatch.localVertexParts _).symm w)=v := by
     have hl:=vertex_local f hf i ((LocalPatch.localVertexParts _).symm w)
     simp only [Equiv.apply_symm_apply] at hl
     rw [←hl]
     exact
       (Fin.val_inj.trans (vertexEquiv f hf).injective.eq_iff)
   by_cases hw : PortPatchAssembly.placeVertex (port f) i ((LocalPatch.localVertexParts _).symm w)=v
   · rw [if_pos (he.mpr hw),if_pos hw]
     change List.map _ ((table (canvasCell f i).shape.kind)[w.val]?.getD []) = _
     rw [←hrow i w,List.map_map]
     apply List.map_congr_left
     intro a _
     change ((before f i).edges.length+a.1.val,a.2)=((edgeEquiv f ⟨i,a.1⟩).val,a.2)
     rw [edgeEquiv_val]
   · rw [if_neg (fun h=>hw (he.mp h)),if_neg hw]
     rfl

 theorem programRow_eq (f : NumericFormula) (hf:NumericValid f)
     (rs : ∀i,RotationRows (patch f i)) (table : RowTable) (hrow:LocalRowLaw f rs table)
     (v : Vertex f) :
     programRow table f.1 (PositiveRoutingCompiler.program f) (vertexEquiv f hf v).val=
       ((rowsFrom f rs).row v).map (eraseStateDart f) := by
   unfold programRow rowsFrom PortPatchAssembly.rotationRows PortPatchAssembly.rowWord
   simp only [List.map_flatMap]
   rw [←canvas_erase,List.length_map,←List.map_coe_finRange,←List.map_reverse,List.flatMap_map]
   apply List.flatMap_congr
   intro i _
   have hop : ((canvas f).map Cell.instruction)[i.val]?.getD (.wire,0,0,0)=
       (canvasCell f i).instruction := by simp [canvasCell]
   rw [hop]
   have hbefore : run f.1 (((canvas f).map Cell.instruction).take i.val)=before f i := by
     simp only [before,run,List.map_take]
   rw [hbefore]
   exact cellRow_eq f hf rs table hrow i v

end PlanarHom.ColoringEmitter.Canvas
