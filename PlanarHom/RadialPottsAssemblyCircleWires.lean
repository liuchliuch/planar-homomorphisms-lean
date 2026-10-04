import PlanarHom.RadialPottsAssemblyOrderedFans
import PlanarHom.RadialPottsAssemblyRowIndices
import PlanarHom.RadialPottsAssemblyClosedWires
import PlanarHom.RadialPottsAssemblyRibbonCircleClip
import PlanarHom.RadialPottsAssemblyDrawingData
import PlanarHom.RadialPottsAssemblyDrawingPortIdentity

/-! Actual corner wires at the exact circle-clipped band ports. All curves,
labels, and closed trace separation are constructed from the original drawing. -/
set_option maxHeartbeats 800000
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph MultiGraph.Kasteleyn Polygonal PlanarityLRRealization
open MultiGraph.PolygonalDrawing
open RadialPottsTile RadialPotts RadialPotts.Assembly

def narrowMap (w : ℝ) (hw : 0<w) (hw1 : w<1) : C(I,I) where
  toFun s := ⟨w*(s:ℝ),mul_nonneg hw.le s.2.1,by nlinarith [s.2.1,s.2.2]⟩
  continuous_toFun := by fun_prop

theorem narrowMap_injective (w : ℝ) (hw : 0<w) (hw1 : w<1) :
    Function.Injective (narrowMap w hw hw1) := by
  intro s t h
  have hh := congrArg (fun x : I => (x:ℝ)) h
  exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hw) hh)

namespace CircleWires
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {d : PolygonalDrawing G}
variable (S : d.TwoSidedStripData) (rays : Dart E→Plane)
variable (F : ∀ a,S.EndpointFan true a (rays a)) (rows : PlanarityLRRealization.RotationRows G)
variable {w : ℝ} (hw : 0<w) (hw1 : w<1) {k : ℕ}

/-- Exact boundary chart heights of each row's actual narrowed fan ports. -/
def heights (v : V) (z : Fin ((rows.row v).length*(2*k))) : ℝ :=
  let p := finProdFinEquiv.symm z
  circleHeight (fanPort S rays F w ((rows.row v).get p.1) p.2)

variable (horder : ∀ v,StrictAnti (heights S rays F rows (w:=w) (k:=k) v))
variable (C : TwoSidedStripData.CircleClipping F (narrowMap w hw hw1))

def corners (v : V) : PlaneDrawing (CornerOrder.graph (rows.row v).length k) :=
  CornerOrder.placedDrawing _ _ (heights S rays F rows v) (horder v)
    (d.drawing.point v) C.radius C.radius_pos

def indexedWire (x : (v : V) × (Fin (rows.row v).length×Fin k)) : C(I,Plane) :=
  (corners S rays F rows hw hw1 horder C x.1).curve x.2

def wire (x : Dart E×Fin k) : C(I,Plane) :=
  indexedWire S rays F rows hw hw1 horder C (RotationRows.wireIndex rows x)

theorem indexedWire_joint_injective
    (x y : (v : V) × (Fin (rows.row v).length×Fin k)) (s t : I)
    (h : indexedWire S rays F rows hw hw1 horder C x s=
      indexedWire S rays F rows hw hw1 horder C y t) : x=y ∧ s=t := by
  rcases x with ⟨v,e⟩
  rcases y with ⟨u,f⟩
  by_cases hvu : v=u
  · subst u
    have hh := CornerOrder.placedDrawing_joint_injective _ _ _ (horder v)
      (d.drawing.point v) C.radius C.radius_pos e f s t h
    exact ⟨congrArg (Sigma.mk v) hh.1,hh.2⟩
  · have hx := CornerOrder.placedDrawing_closed _ _ _ (horder v)
      (d.drawing.point v) C.radius C.radius_pos e s
    have hy := CornerOrder.placedDrawing_closed _ _ _ (horder u)
      (d.drawing.point u) C.radius C.radius_pos f t
    have he : (corners S rays F rows hw hw1 horder C v).curve e s=
      (corners S rays F rows hw hw1 horder C u).curve f t := h
    change rayLength ((corners S rays F rows hw hw1 horder C u).curve f t-d.drawing.point u)≤C.radius at hy
    rw [← he] at hy
    exact (Set.disjoint_left.mp (C.disks_disjoint v u hvu) hx hy).elim

theorem wire_joint_injective (x y : Dart E×Fin k) (s t : I)
    (h : wire S rays F rows hw hw1 horder C x s=wire S rays F rows hw hw1 horder C y t) :
    x=y ∧ s=t := by
  have hh := indexedWire_joint_injective S rays F rows hw hw1 horder C _ _ s t h
  exact ⟨RotationRows.wireIndex_injective rows hh.1,hh.2⟩

theorem wire_inside (x : Dart E×Fin k) (t : I) (ht : Inside t) :
    rayLength (wire S rays F rows hw hw1 horder C x t-d.drawing.point (G.dartPair x.1).1)<C.radius :=
  CornerOrder.placedDrawing_interior _ _ _ (horder (G.dartPair x.1).1)
    (d.drawing.point (G.dartPair x.1).1) C.radius C.radius_pos _ t ht

theorem band_ne_wire (e : E) (p : I×I) (x : Dart E×Fin k) (t : I) (ht : Inside t) :
    C.band (narrowMap_injective w hw hw1) e p ≠ wire S rays F rows hw hw1 horder C x t := by
  intro h
  have hb := C.band_radius_le (narrowMap_injective w hw hw1) e p (G.dartPair x.1).1
  have hh := wire_inside S rays F rows hw hw1 horder C x t ht
  rw [h] at hb
  exact (not_lt_of_ge hb) hh

variable (hne : ∀ a (s : I),((F a).direction (w*(s:ℝ))).1≠0)

include hne in
theorem corners_point (v : V) (i : Fin (rows.row v).length) (j : Fin (2*k)) :
    (corners S rays F rows hw hw1 horder C v).point (i,j)=
      d.drawing.point v+C.radius • circleRay
        ((F ((rows.row v).get i)).direction (w*(orientedLevel portLevel ((rows.row v).get i).2 j:ℝ))) := by
  rw [corners,CornerOrder.placedDrawing_point]
  have hh : heights S rays F rows (w:=w) v (finProdFinEquiv (i,j))=
      circleHeight (fanPort S rays F w ((rows.row v).get i) j) := by
    unfold heights
    rw [Equiv.symm_apply_apply]
  rw [hh]
  unfold fanPort
  rw [diskMap_circleHeight (hne _ _)]

include hne in
theorem wire_zero (x : Dart E×Fin k) :
    wire S rays F rows hw hw1 horder C x 0=
      C.band (narrowMap_injective w hw hw1) (portPreimage rows.rotation x true).1
        (squarePoint (.inr (portPreimage rows.rotation x true).2)) := by
  change (corners S rays F rows hw hw1 horder C (G.dartPair x.1).1).curve
    (RotationRows.rowIndex rows x.1,x.2) 0=
    C.band (narrowMap_injective w hw hw1) x.1.1 (squarePoint (.inr (sideOfBits x.1.2 true,x.2)))
  rw [PlaneDrawing.curve_zero,corners_point S rays F rows hw hw1 horder C hne]
  simp only [CornerOrder.graph,RotationRows.row_get_index]
  rw [C.band_squarePoint_sideOfBits,portIndex_odd,RotationRows.row_get_index]
  rfl

include hne in
theorem wire_one (x : Dart E×Fin k) :
    wire S rays F rows hw hw1 horder C x 1=
      C.band (narrowMap_injective w hw hw1) (portPreimage rows.rotation x false).1
        (squarePoint (.inr (portPreimage rows.rotation x false).2)) := by
  change (corners S rays F rows hw hw1 horder C (G.dartPair x.1).1).curve
    (RotationRows.rowIndex rows x.1,x.2) 1=
    C.band (narrowMap_injective w hw hw1) (rows.rotation x.1).1
      (squarePoint (.inr (sideOfBits (rows.rotation x.1).2 false,reverseLane x.2)))
  rw [PlaneDrawing.curve_one,corners_point S rays F rows hw hw1 horder C hne]
  simp only [CornerOrder.graph,RotationRows.row_get_next]
  rw [C.band_squarePoint_sideOfBits,portIndex_even_reverse,RotationRows.row_get_next,rows.rotation_host]
  rfl

/-- The complete geometric data consumed by the literal terminal-midpoint
assembly construction, with every field proved from actual circles and bands. -/
def drawingData : RadialPotts.Assembly.DrawingData rows.rotation k where
  band := C.band (narrowMap_injective w hw hw1)
  band_joint_injective := C.band_joint_injective (narrowMap_injective w hw hw1)
  wire := wire S rays F rows hw hw1 horder C
  wire_joint_injective := wire_joint_injective S rays F rows hw hw1 horder C
  wire_zero := wire_zero S rays F rows hw hw1 horder C hne
  wire_one := wire_one S rays F rows hw hw1 horder C hne
  band_ne_wire := band_ne_wire S rays F rows hw hw1 horder C

end CircleWires
end PlanarHom.RadialPottsAssemblyGeometry
