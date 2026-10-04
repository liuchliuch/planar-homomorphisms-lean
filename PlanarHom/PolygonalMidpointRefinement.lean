import PlanarHom.PolygonalBandGluing

/-!
# Remove one-segment edges without changing their actual parametrized curves

A single straight segment is replaced by its two midpoint halves. Their standard
path concatenation has exactly the same constant-speed parametrization. Every
nonempty polygonal edge then has at least one internal corner, so pinching its
host endpoints does not collapse the entire candidate ribbon.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.Polygonal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The midpoint of a straight segment, expressed by its affine parametrization. -/
def segmentMiddle (x y : E) : E := AffineMap.lineMap x y (1/2 : ℝ)

theorem segmentMiddle_mem (x y : E) : segmentMiddle x y ∈ [x -[ℝ] y] := by
  rw [segment_eq_image_lineMap]
  exact ⟨1/2,by constructor <;> norm_num,rfl⟩

/-- Two midpoint half-segments concatenate to the same parametrized straight path. -/
theorem segment_halves (x y : E) :
    (Path.segment x (segmentMiddle x y)).trans (Path.segment (segmentMiddle x y) y) =
      Path.segment x y := by
  ext t
  by_cases ht : (t : ℝ) ≤ 1/2
  · simp only [Path.trans_apply,dif_pos ht,Path.segment_apply,segmentMiddle,
      AffineMap.lineMap_apply_module]
    module
  · simp only [Path.trans_apply,dif_neg ht,Path.segment_apply,segmentMiddle,
      AffineMap.lineMap_apply_module]
    module

namespace Chain
variable {U : Set E} {x y : E}

/-- The explicit two-half-segment chain in the original containment set. -/
def halves (h : [x -[ℝ] y] ⊆ U) : Chain U x y :=
  .cons (((convex_segment x y).segment_subset (left_mem_segment ℝ x y)
      (segmentMiddle_mem x y)).trans h)
    (.cons (((convex_segment x y).segment_subset (segmentMiddle_mem x y)
      (right_mem_segment ℝ x y)).trans h) (.nil y (h (right_mem_segment ℝ x y))))

@[simp] theorem length_halves (h : [x -[ℝ] y] ⊆ U) : (halves h).length = 2 := rfl

@[simp] theorem strictPath_halves (h : [x -[ℝ] y] ⊆ U) :
    (halves h).strictPath = Path.segment x y := segment_halves x y

/-- Only length-one chains are refined; all already-longer chains are retained. -/
def refineSingle : {x y : E} → Chain U x y → Chain U x y
  | _, _, .nil x hx => .nil x hx
  | _, _, .cons h (.nil _ _) => halves h
  | _, _, .cons h (.cons k q) => .cons h (.cons k q)

@[simp] theorem strictPath_refineSingle (p : Chain U x y) :
    p.refineSingle.strictPath = p.strictPath := by
  cases p with
  | nil => rfl
  | cons h p =>
    cases p with
    | nil => exact strictPath_halves h
    | cons => rfl

theorem length_refineSingle_ge_two (p : Chain U x y) (hn : p.length ≠ 0) :
    2 ≤ p.refineSingle.length := by
  cases p with
  | nil => exact (hn rfl).elim
  | cons h p =>
    cases p with
    | nil => exact le_rfl
    | cons => simp only [refineSingle,length]; omega

/-- A zero-segment chain is the constant path at its source. -/
theorem strictPath_eq_source_of_length_zero (p : Chain U x y) (h : p.length = 0) (t : I) :
    p.strictPath t = x := by
  cases p with
  | nil => rfl
  | cons h' q => simp [length] at h

end Chain
end PlanarHom.Polygonal

namespace PlanarHom.MultiGraph.PolygonalDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Ordinary drawing avoidance forbids a zero-segment polygonal edge, including a loop. -/
theorem chain_length_ne_zero (d : PolygonalDrawing G) (e : E) : (d.chain e).length ≠ 0 := by
  intro h
  apply d.drawing.interior_avoids e PlaneDrawing.half PlaneDrawing.half_inside (G.src e)
  rw [d.curve_eq]
  exact (d.chain e).strictPath_eq_source_of_length_zero h PlaneDrawing.half

/-- Refine short polygonal chains while retaining exactly the old ordinary drawing. -/
def refineSingle (d : PolygonalDrawing G) : PolygonalDrawing G where
  drawing := d.drawing
  chain e := (d.chain e).refineSingle
  curve_eq e := by rw [Polygonal.Chain.strictPath_refineSingle]; exact d.curve_eq e

/-- Every refined edge has at least one genuine internal chain vertex. -/
theorem refineSingle_chain_length (d : PolygonalDrawing G) (e : E) :
    2 ≤ (d.refineSingle.chain e).length :=
  (d.chain e).length_refineSingle_ge_two (d.chain_length_ne_zero e)

end PlanarHom.MultiGraph.PolygonalDrawing
