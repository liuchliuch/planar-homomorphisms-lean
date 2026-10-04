import PlanarHom.PolygonalDrawingIncidence

/-!
# Refined straight pieces cannot join two original host vertices

The proof uses the real dyadic subpath parametrization. A nonempty right tail
can meet a host only at the original final endpoint; each nondegenerate segment
in that tail therefore has a non-host endpoint. The first join is an interior
parameter of the original edge and is likewise not a host.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.Polygonal
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
theorem right_tail_host_is_target {x a y : X} (p : Path x a) (q : Path a y) (H : Set X)
    (havoid : ∀ t : I, MultiGraph.Inside t → (p.trans q) t ∉ H)
    {w : X} (hw : w ∈ Set.range q) (hwH : w ∈ H) : w = y := by
  obtain ⟨u,hu⟩ := hw
  by_cases hu1 : u = 1
  · simpa [hu1] using hu.symm
  · have hu' : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 (fun h => hu1 (Subtype.ext h))
    have hi : MultiGraph.Inside (MultiGraph.PlaneDrawing.halfParameter true u) := by
      constructor <;> dsimp [MultiGraph.PlaneDrawing.halfParameter] <;> linarith [u.2.1]
    exact (havoid _ hi (by rw [trans_right_half,hu]; exact hwH)).elim

namespace Chain
variable {U H : Set X} {x y : X}

/-- For an embedded chain of at least two segments, every piece has a non-host endpoint. -/
theorem segment_has_nonhost_endpoint (p : Chain U x y) (hp : GraphArc p.strictPath)
    (havoid : ∀ t : I, MultiGraph.Inside t → p.strictPath t ∉ H)
    (hlen : 2 ≤ p.length) {a b : X} (hab : (a,b) ∈ p.segments) : a ∉ H ∨ b ∉ H := by
  by_contra hn
  have hh : a ∈ H ∧ b ∈ H := by simpa using hn
  cases p with
  | nil => simp [length] at hlen
  | @cons x c y h p =>
    cases p with
    | nil => simp [length] at hlen
    | @cons c d y k q =>
      rcases List.mem_cons.mp hab with heq | hab
      · cases heq
        have hj := trans_right_half (Path.segment x b) (Chain.cons k q).strictPath (0 : I)
        rw [MultiGraph.PlaneDrawing.halfParameter_true_zero] at hj
        exact havoid MultiGraph.PlaneDrawing.half MultiGraph.PlaneDrawing.half_inside
          (by
            change ((Path.segment x b).trans (Chain.cons k q).strictPath) MultiGraph.PlaneDrawing.half ∈ H
            rw [hj]
            simpa using hh.2)
      · have ha : a = y := right_tail_host_is_target (Path.segment x c) (Chain.cons k q).strictPath H havoid
          (by
            rw [Chain.range_strictPath]
            exact (Chain.cons k q).segment_subset_support hab (left_mem_segment ℝ a b)) hh.1
        have hb : b = y := right_tail_host_is_target (Path.segment x c) (Chain.cons k q).strictPath H havoid
          (by
            rw [Chain.range_strictPath]
            exact (Chain.cons k q).segment_subset_support hab (right_mem_segment ℝ a b)) hh.2
        exact (Chain.cons h (Chain.cons k q)).graphArc_segment_ne hp
          (List.mem_cons_of_mem _ hab) (ha.trans hb.symm)

end Chain
end PlanarHom.Polygonal

namespace PlanarHom.MultiGraph.PolygonalDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Host avoidance is preserved by the exact polygonal chain parametrization. -/
theorem chain_interior_avoids_hosts (d : PolygonalDrawing G) (e : E) (t : I) (ht : Inside t) :
    (d.chain e).strictPath t ∉ d.hostSet := by
  rintro ⟨v,hv⟩
  apply d.drawing.interior_avoids e t ht v
  rw [d.curve_eq]
  exact hv.symm

/-- The midpoint refinement discharges the free-endpoint premise for every
actual source graph, without adding any certificate to the planar promise. -/
theorem refined_segment_has_nonhost_endpoint (d : PolygonalDrawing G) {a b : Plane}
    (hab : (a,b) ∈ d.refineSingle.segmentSet) :
    a ∉ d.refineSingle.hostSet ∨ b ∉ d.refineSingle.hostSet := by
  obtain ⟨e,he⟩ := hab
  exact (d.refineSingle.chain e).segment_has_nonhost_endpoint
    (d.refineSingle.chain_graphArc e) (d.refineSingle.chain_interior_avoids_hosts e)
    (d.refineSingle_chain_length e) he

end PlanarHom.MultiGraph.PolygonalDrawing
