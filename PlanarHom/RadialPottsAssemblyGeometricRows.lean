import PlanarHom.RadialPottsAssemblyCircleWires
import PlanarHom.RadialPottsAssemblyDrawingGluing

/-! NEW genuine radial assembly from an actual polygonal source canvas and its
geometric clockwise rows. The source rows may have arbitrary degree and either
half-plane may contain many germs. Every band, corner wire, tile, and final
curve is constructed by the proved geometric algorithms. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization RadialPottsAssemblyGeometry
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E}

theorem polygonal_drawingData_of_clockwiseRows (d : PolygonalDrawing G)
    (rays : Dart E→Plane)
    (hgerm : ∀a,StraightGerm (d.drawing.dartPath a) (d.drawing.point (G.dartPair a).1) (rays a))
    (rows : RotationRows G) (hne : ∀a,(rays a).1≠0)
    (hrows : ∀v,(rows.row v).Pairwise (fun a b=>ClockwiseRayOrder (rays a) (rays b)))
    (k : ℕ) : Nonempty (DrawingData rows.rotation k) := by
  obtain ⟨S,F,hclip⟩ := d.exists_refined_fans_and_circleClippings true rays hgerm
  obtain ⟨w,hw,hw1,hport,horder⟩ := exists_uniform_clockwise_fan_width S rays F rows hne hrows k
  obtain ⟨C⟩ := hclip (narrowMap w hw hw1) (narrowMap_injective w hw hw1)
  exact ⟨CircleWires.drawingData S rays F rows hw hw1 horder C hport⟩

def drawing_of_clockwiseRows (d : PolygonalDrawing G) (rays : Dart E→Plane)
    (hgerm : ∀a,StraightGerm (d.drawing.dartPath a) (d.drawing.point (G.dartPair a).1) (rays a))
    (rows : RotationRows G) (hne : ∀a,(rays a).1≠0)
    (hrows : ∀v,(rows.row v).Pairwise (fun a b=>ClockwiseRayOrder (rays a) (rays b)))
    (k : ℕ) : PlaneDrawing (graph rows.rotation k) :=
  (Classical.choice (polygonal_drawingData_of_clockwiseRows d rays hgerm rows hne hrows k)).drawing

theorem planar_of_clockwiseRows (d : PolygonalDrawing G) (rays : Dart E→Plane)
    (hgerm : ∀a,StraightGerm (d.drawing.dartPath a) (d.drawing.point (G.dartPair a).1) (rays a))
    (rows : RotationRows G) (hne : ∀a,(rays a).1≠0)
    (hrows : ∀v,(rows.row v).Pairwise (fun a b=>ClockwiseRayOrder (rays a) (rays b)))
    (k : ℕ) : (graph rows.rotation k).Planar :=
  ⟨drawing_of_clockwiseRows d rays hgerm rows hne hrows k⟩

end PlanarHom.RadialPotts.Assembly
