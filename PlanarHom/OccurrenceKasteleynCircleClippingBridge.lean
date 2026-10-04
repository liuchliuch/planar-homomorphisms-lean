import PlanarHom.RadialPottsAssemblyRibbonCircleClip

/-!
# NEW unconditional polygonal fan-and-circle-clipping bridge

Every endpoint germ is derived from its literal first/last polygonal piece.
The recovered circle-clipping theorem then needs no extra germ certificate.
-/
noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing
open Polygonal Kasteleyn PlanarityLRRealization TwoSidedStripData
variable {V E : Type*} {G : MultiGraph V E}

/-- Every literal directed occurrence has an actual positive straight germ with
nonzero ray, derived from the finite polygonal chain. -/
theorem exists_dart_straightGerm (d : PolygonalDrawing G) (a : Dart E) :
    ∃ ray : Plane, ray≠0 ∧
      StraightGerm (d.drawing.dartPath a) (d.drawing.point (G.dartPair a).1) ray := by
  rcases a with ⟨e,b⟩
  cases b
  · obtain ⟨z,ε,k,hz,hε,hk,hform⟩ :=
      (d.chain e).vertexBand_uniform_target (d.chain_length_ne_zero e) id rfl
    refine ⟨z-d.drawing.point (G.dst e),
      sub_ne_zero.mpr (d.segment_ne ⟨e,hz⟩),ε,k,hε,hk,?_⟩
    intro t ht
    have hh := hform t ht (0 : I)
    simp only [Chain.vertexBand_zero_transverse] at hh
    change d.drawing.curve e (unitInterval.symm t) = _
    rw [d.curve_eq]
    simpa [dartPair] using hh
  · obtain ⟨z,ε,k,hz,hε,hk,hform⟩ :=
      (d.chain e).vertexBand_uniform_source (d.chain_length_ne_zero e) id rfl
    refine ⟨z-d.drawing.point (G.src e),
      sub_ne_zero.mpr (d.segment_ne ⟨e,hz⟩).symm,ε,k,hε,hk,?_⟩
    intro t ht
    have hh := hform t ht (0 : I)
    simp only [Chain.vertexBand_zero_transverse] at hh
    change d.drawing.curve e t = _
    rw [d.curve_eq]
    simpa [dartPair] using hh

variable [Fintype V] [Fintype E]

/-- Original-curve-preserving normal collars, nonzero endpoint fans and a common
circle clipping are all obtained from the drawing alone, including loops. -/
theorem exists_refined_circleClipping (d : PolygonalDrawing G) (positive : Bool) :
    ∃ D : d.refineSingle.TwoSidedStripData,
      ∃ rays : Dart E → Plane, (∀ a, rays a≠0) ∧
      ∃ F : ∀ a, D.EndpointFan positive a (rays a),
        Nonempty (CircleClipping F (ContinuousMap.id I)) := by
  choose rays hne hgerm using d.exists_dart_straightGerm
  obtain ⟨D,F,hF⟩ := d.exists_refined_fans_and_circleClippings positive rays hgerm
  exact ⟨D,rays,hne,F,hF (ContinuousMap.id I) Function.injective_id⟩

end PlanarHom.MultiGraph.PolygonalDrawing
namespace PlanarHom.MultiGraph
open Kasteleyn PolygonalDrawing.TwoSidedStripData
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}

/-- The entry point still accepts only ordinary finite multigraph planarity. -/
theorem Planar.exists_polygonal_circleClipping (h : G.Planar) (positive : Bool) :
    ∃ d : PolygonalDrawing G, ∃ D : d.refineSingle.TwoSidedStripData,
      ∃ rays : Dart E → Plane, (∀ a, rays a≠0) ∧
      ∃ F : ∀ a, D.EndpointFan positive a (rays a),
        Nonempty (CircleClipping F (ContinuousMap.id I)) := by
  obtain ⟨d⟩ := h.exists_polygonalDrawing
  exact ⟨d,d.exists_refined_circleClipping positive⟩

end PlanarHom.MultiGraph
