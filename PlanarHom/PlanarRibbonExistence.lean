import PlanarHom.PlanarPolygonalization
import PlanarHom.PolygonalFiniteIncidence
import PlanarHom.PolygonalEndpointIntersections
import PlanarHom.PolygonalRibbonAssembly
import PlanarHom.ReplicationPlanarity

/-!
# Unrestricted finite planarity admits explicit ribbons

The entire chain is proved: arbitrary continuous ordinary drawings are redrawn
polygonally; length-one chains receive their exact midpoint refinement; actual
finite segment incidence yields shared corner normals and one positive safe
width; the jointly continuous bands satisfy the original ribbon conditions.

No embedding or ribbon certificate is added to the abstract graph input or its
serialized planar promise. Consequently uniform and selected-label thickening
preserve ordinary planarity for the actual compiler outputs, including loops,
parallel occurrences, zero copy counts and isolated vertices.
-/

noncomputable section
open Set
namespace PlanarHom.MultiGraph
namespace PolygonalDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Construct ribbons from every finite polygonal drawing. All local width and
incidence conditions are discharged from the drawing, not supplied as assumptions. -/
theorem exists_ribbonDrawing [Finite V] [Finite E] (d : PolygonalDrawing G) :
    Nonempty (RibbonDrawing G) := by
  let p := d.refineSingle
  let S := p.segmentFinset
  have hS : (S : Set (Plane × Plane)) = p.segmentSet := p.coe_segmentFinset
  have hcorner : Polygonal.TwoValentCorners (S : Set (Plane × Plane)) p.hostSet := by
    rw [hS]
    exact p.twoValentCorners
  have hpair : Polygonal.EndpointIntersections (S : Set (Plane × Plane)) := by
    rw [hS]
    exact p.endpointIntersections
  have hne : ∀ e ∈ S, e.1 ≠ e.2 := by
    intro e he
    exact p.segment_ne ((p.mem_segmentFinset e).mp he)
  have hvertex : Polygonal.HostEndpointOnly (S : Set (Plane × Plane)) p.hostSet := by
    intro e he X hX hcontact
    rcases p.host_segment_contact ((p.mem_segmentFinset e).mp he) hX hcontact with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hfree : ∀ a b, (a,b) ∈ S → a ∉ p.hostSet ∨ b ∉ p.hostSet := by
    intro a b hab
    exact d.refined_segment_has_nonhost_endpoint ((p.mem_segmentFinset (a,b)).mp hab)
  obtain ⟨N,ε,hzero,_,_,hgood⟩ := Polygonal.exists_normal_and_good_width S p.hostSet
    p.finite_hostSet hcorner hpair hne hvertex hfree 1 zero_lt_one
  exact ⟨p.ribbonOfGoodWidth S (fun e q hq => p.chain_segment_mem_finset e hq) N ε hzero hgood⟩

end PolygonalDrawing

/-- The critical unrestricted bridge: every finite ordinary planar multigraph
has genuine explicit disjoint pinched edge neighborhoods. -/
theorem Planar.exists_ribbonDrawing {V E : Type*} [Finite V] [Finite E]
    {G : MultiGraph V E} (h : G.Planar) : Nonempty (RibbonDrawing G) := by
  obtain ⟨p⟩ := h.exists_polygonalDrawing
  exact p.exists_ribbonDrawing

/-- Ribbon existence and ordinary abstract planarity are equivalent for finite
multigraphs. Neither direction changes the source-input convention. -/
theorem planar_iff_ribbonDrawing {V E : Type*} [Finite V] [Finite E] (G : MultiGraph V E) :
    G.Planar ↔ Nonempty (RibbonDrawing G) :=
  ⟨Planar.exists_ribbonDrawing,fun ⟨d⟩ => d.planar⟩

/-- Unconditional ordinary planarity preservation under uniform thickening. -/
theorem Planar.thicken {V E : Type*} [Finite V] [Finite E] {G : MultiGraph V E}
    (h : G.Planar) (n : ℕ) : (G.thicken n).Planar := by
  obtain ⟨d⟩ := h.exists_ribbonDrawing
  exact d.thicken_planar n

/-- Unconditional ordinary planarity preservation under arbitrary finite
occurrence-dependent copy counts. -/
theorem Planar.replicateOccurrences {V E : Type*} [Finite V] [Finite E]
    {G : MultiGraph V E} (h : G.Planar) (count : E → ℕ) :
    (G.replicateOccurrences count).Planar := by
  obtain ⟨d⟩ := h.exists_ribbonDrawing
  exact d.replicate_planar count

end PlanarHom.MultiGraph

namespace PlanarHom.Complexity.GraphCode

/-- The actual serialized uniform-thickening query satisfies the original planar
promise for every ordinary planar source code. No certificate is input data. -/
theorem PlanarValid.parallel {g : GraphCode} (h : g.PlanarValid) (n : ℕ) :
    (g.parallel n).PlanarValid := by
  obtain ⟨hg,hp⟩ := h
  obtain ⟨d⟩ := hp.exists_ribbonDrawing
  exact g.parallel_planar_of_ribbon hg d n

/-- The actual variable-copy occurrence-list output also preserves the raw promise. -/
theorem PlanarValid.replicateOccurrences {g : GraphCode} (h : g.PlanarValid)
    (count : (ℕ × ℕ) → ℕ) : (g.replicateOccurrences count).PlanarValid := by
  obtain ⟨hg,hp⟩ := h
  obtain ⟨d⟩ := hp.exists_ribbonDrawing
  exact g.replicate_planar_of_ribbon hg d count

end PlanarHom.Complexity.GraphCode

namespace PlanarHom.Complexity.MixedCode

/-- Selected-label compiler queries are unconditionally ordinary-planar. All
unchanged labels/unaries retain their established exact occurrence semantics. -/
theorem PlanarValid.parallelLabel {binaryTypes unaryTypes : ℕ} {g : MixedCode}
    (h : g.PlanarValid binaryTypes unaryTypes) (selected n : ℕ) :
    (g.parallelLabel selected n).PlanarValid binaryTypes unaryTypes := by
  have hp := (g.planarValid_iff h.1).mp h
  obtain ⟨d⟩ := hp.exists_ribbonDrawing
  exact g.parallelLabel_planar_of_ribbon h.1 d selected n

end PlanarHom.Complexity.MixedCode
