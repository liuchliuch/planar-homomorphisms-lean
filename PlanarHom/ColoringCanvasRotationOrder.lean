import PlanarHom.PortPatchRotationOrder
import PlanarHom.ColoringCanvasRotationRows
import PlanarHom.ColoringCanvasCrossBlockOrder
import PlanarHom.ColoringCanvasDartRays

/-! NEW actual clockwise concatenation of the emitter's reverse-cell rows.
Only the finite local-row clockwise tables remain as a premise of this
intermediate lemma; all global placement/order/ray facts are discharged. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree
open PlanarityLRRealization RadialPottsAssemblyGeometry

 theorem rowsFrom_clockwise (D:MacroGeometry.RawDrawings) (f:NumericFormula)
    (rs:∀i,RotationRows (patch f i))
    (hlocal:∀i w,((rs i).row w).Pairwise (fun a b=>
      ClockwiseRayOrder (MacroGeometry.ray (canvasCell f i).shape a)
        (MacroGeometry.ray (canvasCell f i).shape b))) (v:Vertex f) :
    ((rowsFrom f rs).row v).Pairwise (fun a b=>
      ClockwiseRayOrder ((shearedDrawingFrom D f).endpointRay a)
        ((shearedDrawingFrom D f).endpointRay b)) := by
  apply PortPatchAssembly.rotationRows_pairwise
  · exact placeVertex_injective f
  · intro i hi w hw
    apply List.pairwise_map.mpr
    apply (hlocal i w).imp
    intro a b hab
    change ClockwiseRayOrder ((shearedDrawingFrom D f).endpointRay (liftDart f i a))
      ((shearedDrawingFrom D f).endpointRay (liftDart f i b))
    simpa only [sheared_endpointRay] using hab
  · have ho:((List.finRange (canvas f).length).reverse).Pairwise (fun (i j : Fin (canvas f).length) => j < i) := by
      simpa only [List.pairwise_reverse] using List.pairwise_lt_finRange (canvas f).length
    apply ho.imp
    intro i j hji a ha b hb
    have ha':PortPatchAssembly.placeVertex (port f) i ((patch f i).dartPair a).1=v:=
      (PortPatchAssembly.localRowWord_mem (patch f) (port f) rs (localVertices f) (localVertices_mem f) i v a).mp ha
    have hb':PortPatchAssembly.placeVertex (port f) j ((patch f j).dartPair b).1=v:=
      (PortPatchAssembly.localRowWord_mem (patch f) (port f) rs (localVertices f) (localVertices_mem f) j v b).mp hb
    change ClockwiseRayOrder ((shearedDrawingFrom D f).endpointRay (liftDart f i a))
      ((shearedDrawingFrom D f).endpointRay (liftDart f j b))
    rw [sheared_endpointRay,sheared_endpointRay]
    exact cross_block_clockwise f i j hji a b (ha'.trans hb'.symm)

end PlanarHom.ColoringEmitter.Canvas
