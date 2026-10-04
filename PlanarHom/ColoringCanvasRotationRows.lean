import PlanarHom.ColoringEmitterCanvas
import PlanarHom.PortPatchRotationRows

/-! NEW actual canvas rotation rows: reverse cell order, preserving each
fixed local cyclic order at the uniquely shared or private local vertex. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree PlanarityLRRealization

 def localVertices (f : NumericFormula) (i : Index f) : List (Port f i ⊕ Private f i) :=
   (List.finRange (Macro.vertexCount (canvasCell f i).shape.kind)).map
     (LocalPatch.localVertexParts (canvasCell f i).shape).symm

 theorem localVertices_nodup (f : NumericFormula) (i : Index f) : (localVertices f i).Nodup :=
   (List.nodup_finRange _).map (LocalPatch.localVertexParts _).symm.injective

 theorem localVertices_mem (f : NumericFormula) (i : Index f) (v : Port f i ⊕ Private f i) :
     v∈localVertices f i := by
   simp only [localVertices,List.mem_map]
   exact ⟨LocalPatch.localVertexParts _ v,List.mem_finRange _,by simp⟩

 def rowsFrom (f : NumericFormula) (rs : ∀i,RotationRows (patch f i)) : RotationRows (graph f) :=
   PortPatchAssembly.rotationRows (patch f) (port f) rs (localVertices f)
     (localVertices_nodup f) (localVertices_mem f) (List.finRange (canvas f).length).reverse
     (List.nodup_reverse.mpr (List.nodup_finRange _)) (by intro i; simp)

 theorem port_injective (f : NumericFormula) (i : Index f) : Function.Injective (port f i) := by
   rintro ⟨p,a⟩ ⟨q,b⟩ h
   have hsignal:=congrArg Prod.fst h
   have hpos:=congrArg (fun s:Boundary f=>s.val) hsignal
   have hp:= (canvasCell f i).port_positions_injective hpos
   exact Prod.ext hp (congrArg (fun a:BoundaryTriple f=>a.2) h)

 theorem placeVertex_injective (f : NumericFormula) (i : Index f) :
     Function.Injective (PortPatchAssembly.placeVertex (W:=Private f) (port f) i) := by
   intro v w h
   cases v with
   | inl v =>
     cases w with
     | inl w => exact congrArg Sum.inl (port_injective f i (Sum.inl.inj h))
     | inr w => contradiction
   | inr v =>
     cases w with
     | inl w => contradiction
     | inr w => exact congrArg Sum.inr (by simpa only [PortPatchAssembly.placeVertex,Sum.inr.injEq,Sigma.mk.inj_iff,heq_eq_eq,true_and] using h)

end PlanarHom.ColoringEmitter.Canvas
