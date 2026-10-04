import PlanarHom.PlanarityLRComponentContour
import PlanarHom.PlanarityLRComponentTreeCardinality
import PlanarHom.PlanarityLRRawPortNoncrossing
import PlanarHom.PlanarityLRForestEuler

/-! NEW Euler equality for the literal computed rotation on every nonempty
actual DFS component. All contour, forest-size and noncrossing inputs are proved
from the executable LR output, with no geometric Euler certificate. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open PlanarityDepthFirstSearch PlanarityLRConstraints PlanarityLRConstraintBlocks FinitePermutationCycles

theorem component_euler_of_alignedLR (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (hLR : LRCondition g (bitSide bits))
    (halign : Aligned (bitSide bits) (alignmentPairs g))
    (r : Fin g.vertices) (hr : height g r.val=0) [Nonempty (ComponentEdge g r.val)] :
    Nat.card (ComponentVertex g r.val)+count (componentFace g hg r.val (directRotationRows g hg bits))=
      Nat.card (ComponentEdge g r.val)+2 := by
  let base : Dart (ComponentEdge g r.val) := (Classical.choice inferInstance,true)
  let a := computedComponentStart g hg bits r.val base
  let rows := componentRows g hg r.val (directRotationRows g hg bits)
  let selected := componentSelected g r.val
  let key := fun p : Dart {e : ComponentEdge g r.val // selected e=false} =>
    contourKey g bits (eraseDart (p.1.val.val,p.2))
  have hsingle : ∀x, Equiv.Perm.SameCycle ((partialReverse (ComponentEdge g r.val) selected).trans rows.rotation) a x :=
    fun x => componentContour_singleCycle g hg r.val (directRotationRows g hg bits) a x
  have hsort : (visibleContourWord rows.rotation selected a).Pairwise (fun x y => key x<key y) := by
    have hs := componentPortWord_key_sorted g hg bits (componentDartLift g r.val base)
    rw [←componentVisibleWord_lift g hg bits r.val base] at hs
    rw [List.pairwise_map] at hs
    exact hs
  have horder : ∀e f : {e : ComponentEdge g r.val // selected e=false}, e≠f →
      PortNoncrossing (key (e,true)) (key (e,false)) (key (f,true)) (key (f,false)) := by
    intro e f hef
    have hne : e.val.val.val≠f.val.val.val := by
      intro h
      apply hef
      apply Subtype.ext
      apply Subtype.ext
      exact Fin.ext h
    exact nonTree_raw_port_key_noncrossing g hg bits hLR halign e.val.val.isLt f.val.val.isLt
      e.property f.property hne (e.val.property.trans f.val.property.symm)
  exact euler_of_single_forest_contour (V:=ComponentVertex g r.val) rows.rotation selected a hsingle
    (component_selected_edges_add_one g hg r hr) key hsort horder

/-- Every actually accepting aligned-LR computation has genus-zero component
rotations, including the connected tree case with no non-tree occurrence. -/
theorem component_euler_of_accepts (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (hflag : (decideAligned g).1=true) (r : Fin g.vertices) (hr : height g r.val=0)
    [Nonempty (ComponentEdge g r.val)] :
    Nat.card (ComponentVertex g r.val)+
      count (componentFace g hg r.val (directRotationRows g hg (decideAligned g).2))=
      Nat.card (ComponentEdge g r.val)+2 :=
  component_euler_of_alignedLR g hg (decideAligned g).2 (decideAligned_sound g hflag).1
    (decideAligned_sound g hflag).2 r hr

/-- Isolated vertices keep zero literal face cycles and no runtime table row. -/
theorem component_isolated_face_count (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (r : ℕ) [IsEmpty (ComponentEdge g r)] :
    count (componentFace g hg r (directRotationRows g hg bits))=0 := count_empty _

end PlanarHom.PlanarityLRRealization
