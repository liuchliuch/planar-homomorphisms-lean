import PlanarHom.OccurrenceKasteleynRecenteredCollars

/-!
# NEW proof: finite ordinary planarity admits polygonal two-sided face collars

The preceding recentering construction is polygonal when applied to the proved
vertex-interpolation ribbons. This module proves that fact, then constructs the
ribbons, their common midpoint drawing, and the actual complementary side faces
from the ordinary finite-planarity hypothesis alone.
-/

noncomputable section
open Set unitInterval
namespace PlanarHom.Polygonal.Chain
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {U : Set X} {x y : X}

/-- Every constant-height slice is the strict path of the explicitly
interpolated finite vertex list; the vertex map need not be continuous. -/
theorem vertexBand_slice (p : Chain U x y) (f : X → X) (s t : I) :
    p.vertexBand f (t,s) =
      (p.mapVertices (fun v => v+(s : ℝ) • (f v-v))).strictPath t := by
  induction p generalizing t with
  | nil => simp [vertexBand,strictPath,mapVertices]
  | @cons x a y h p ih =>
    cases p with
    | nil a ha =>
      simp only [vertexBand,ContinuousMap.coe_mk,strictPath,mapVertices,Path.segment_apply,
        AffineMap.lineMap_apply_module]
      module
    | @cons a b y k q =>
      by_cases ht : (t : ℝ) ≤ 1/2
      · simp only [vertexBand,ContinuousMap.coe_mk,strictPath,mapVertices,Path.trans_apply,
          dif_pos ht,Path.segment_apply,AffineMap.lineMap_apply_module]
        module
      · let u : I := ⟨2*(t : ℝ)-1,by constructor <;> linarith [t.2.2]⟩
        simpa only [vertexBand,ContinuousMap.coe_mk,strictPath,mapVertices,Path.trans_apply,
          dif_neg ht] using ih u

/-- If both endpoints are fixed, the polygonal slice has those same endpoints. -/
theorem exists_vertexBand_slice (p : Chain U x y) (f : X → X)
    (hx : f x = x) (hy : f y = y) (s : I) :
    ∃ q : Chain Set.univ x y, ∀ t : I, p.vertexBand f (t,s) = q.strictPath t := by
  let g : X → X := fun v => v+(s : ℝ) • (f v-v)
  have hgx : g x = x := by simp [g,hx]
  have hgy : g y = y := by simp [g,hy]
  have h := p.vertexBand_slice f s
  change ∀ t, p.vertexBand f (t,s) = (p.mapVertices g).strictPath t at h
  generalize p.mapVertices g = q at h
  revert q h
  rw [hgx,hgy]
  intro q h
  exact ⟨q,h⟩

end PlanarHom.Polygonal.Chain

namespace PlanarHom.MultiGraph.PolygonalDrawing
open PlanarHom.Polygonal
variable {V E : Type*} {G : MultiGraph V E}

/-- Slices of the actual good-width ribbon are still explicit finite polygonal
drawings. This supplies the polygonality needed for the subsequent face theory. -/
theorem exists_polygonal_slice (d : PolygonalDrawing G) (S : Finset (Plane × Plane))
    (hS : ∀ e p, p ∈ (d.chain e).segments → p ∈ S)
    (N : Plane → Plane) (ε : ℝ) (hzero : ∀ x ∈ d.hostSet, N x = 0)
    (hgood : GoodStripWidth S d.hostSet N ε) (s : I) :
    ∃ p : PolygonalDrawing G,
      p.drawing = (d.ribbonOfGoodWidth S hS N ε hzero hgood).sliceDrawing s := by
  let R := d.ribbonOfGoodWidth S hS N ε hzero hgood
  have hpoly (e : E) : ∃ q : Chain Set.univ (d.drawing.point (G.src e))
      (d.drawing.point (G.dst e)), ∀ t : I, R.band e (t,s) = q.strictPath t := by
    exact (d.chain e).exists_vertexBand_slice (fun v => v+ε • N v)
      (by simp [hzero _ ⟨G.src e,rfl⟩]) (by simp [hzero _ ⟨G.dst e,rfl⟩]) s
  choose q hq using hpoly
  refine ⟨⟨R.sliceDrawing s,q,?_⟩,rfl⟩
  intro e
  apply ContinuousMap.ext
  intro t
  exact hq e t

end PlanarHom.MultiGraph.PolygonalDrawing

namespace PlanarHom.MultiGraph.PolygonalDrawing
open PlanarHom.Polygonal
variable {V E : Type*} {G : MultiGraph V E}

/-- Construct a polygonal midpoint drawing of genuine two-sided ribbons from
any finite polygonal drawing. All original vertex positions are retained. -/
theorem exists_polygonal_ribbon_center [Finite V] [Finite E] (d : PolygonalDrawing G) :
    ∃ (R : RibbonDrawing G) (p : PolygonalDrawing G),
      p.drawing = R.centerDrawing ∧ p.drawing.point = d.drawing.point := by
  let q := d.refineSingle
  let S := q.segmentFinset
  have hS : (S : Set (Plane × Plane)) = q.segmentSet := q.coe_segmentFinset
  have hcorner : TwoValentCorners (S : Set (Plane × Plane)) q.hostSet := by
    rw [hS]
    exact q.twoValentCorners
  have hpair : EndpointIntersections (S : Set (Plane × Plane)) := by
    rw [hS]
    exact q.endpointIntersections
  have hne : ∀ e ∈ S, e.1 ≠ e.2 := by
    intro e he
    exact q.segment_ne ((q.mem_segmentFinset e).mp he)
  have hvertex : HostEndpointOnly (S : Set (Plane × Plane)) q.hostSet := by
    intro e he X hX hcontact
    rcases q.host_segment_contact ((q.mem_segmentFinset e).mp he) hX hcontact with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hfree : ∀ a b, (a,b) ∈ S → a ∉ q.hostSet ∨ b ∉ q.hostSet := by
    intro a b hab
    exact d.refined_segment_has_nonhost_endpoint ((q.mem_segmentFinset (a,b)).mp hab)
  obtain ⟨N,ε,hzero,_,_,hgood⟩ := exists_normal_and_good_width S q.hostSet
    q.finite_hostSet hcorner hpair hne hvertex hfree 1 zero_lt_one
  have hpieces : ∀ e z, z ∈ (q.chain e).segments → z ∈ S :=
    fun e _ hz => q.chain_segment_mem_finset e hz
  let R := q.ribbonOfGoodWidth S hpieces N ε hzero hgood
  obtain ⟨p,hp⟩ := q.exists_polygonal_slice S hpieces N ε hzero hgood PlaneDrawing.half
  refine ⟨R,p,hp,?_⟩
  rw [hp]
  rfl

end PlanarHom.MultiGraph.PolygonalDrawing

namespace PlanarHom.MultiGraph
variable {V E : Type*} {G : MultiGraph V E}

/-- Unconditional two-sided collar existence in the required polygonal category.
The input remains the ordinary finite-planarity predicate, not a rotation-system,
Euler, embedding or orientation certificate. The two actual complementary faces
and closure-incidence proofs are the `RibbonDrawing.sideFace` API. -/
theorem Planar.exists_polygonal_ribbon_center [Finite V] [Finite E] (h : G.Planar) :
    ∃ (R : RibbonDrawing G) (p : PolygonalDrawing G), p.drawing = R.centerDrawing := by
  obtain ⟨d⟩ := h.exists_polygonalDrawing
  obtain ⟨R,p,hp,_⟩ := d.exists_polygonal_ribbon_center
  exact ⟨R,p,hp⟩

/-- Self-contained face-incidence endpoint: every ordinary finite planar graph
has a polygonal drawing in which each occurrence has two disjoint connected
collar sides, each contained in a real complementary component, with its entire
closed edge in that component's closure. The two components may coincide. -/
theorem Planar.exists_polygonal_two_sided_face_collars [Finite V] [Finite E] (h : G.Planar) :
    ∃ (p : PolygonalDrawing G) (R : RibbonDrawing G), p.drawing = R.centerDrawing ∧
      (∀ (b : Bool) (e : E),
        IsConnected (R.sideRegion b e) ∧
        R.sideRegion b e ⊆ p.drawing.supportᶜ ∧
        R.sideRegion b e ⊆ R.sideFace b e ∧
        IsConnected (R.sideFace b e) ∧
        Set.range (p.drawing.curve e) ⊆ closure (R.sideFace b e)) ∧
      (∀ (b c : Bool) (e f : E), (e,b) ≠ (f,c) →
        Disjoint (R.sideRegion b e) (R.sideRegion c f)) := by
  obtain ⟨R,p,hp⟩ := h.exists_polygonal_ribbon_center
  refine ⟨p,R,hp,?_,?_⟩
  · intro b e
    refine ⟨R.sideRegion_isConnected b e,?_,R.sideRegion_subset_sideFace b e,
      R.sideFace_isConnected b e,?_⟩
    · rw [hp]
      exact R.sideRegion_subset_compl b e
    · rintro _ ⟨t,rfl⟩
      rw [hp]
      exact R.curve_mem_closure_sideFace b e t
  · intro b c e f hne
    exact R.sideRegion_disjoint hne

end PlanarHom.MultiGraph
