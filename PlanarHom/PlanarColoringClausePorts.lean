import PlanarHom.PlanarColoringClauseDrawing
import PlanarHom.PlanarTransport

/-! A concrete nine-port polygonal patch interface for the exact-one color
clause. The region includes owned open rim edges and excludes all port points;
its vertex/curve membership facts are proved from the actual integer drawing. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.PlanarColoringClause
open MultiGraph IntegerStraightDrawing
set_option maxHeartbeats 5000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000

def boundary : Fin 9 → Vertex :=
  ![copyVertex 0 0,copyVertex 0 2,copyVertex 1 6,
    copyVertex 1 0,copyVertex 1 2,copyVertex 2 6,
    copyVertex 2 0,copyVertex 2 2,copyVertex 0 6]

def IsPort (v : Vertex) : Prop := ∃ k,boundary k=v
instance (v : Vertex) : Decidable (IsPort v) := by unfold IsPort; infer_instance

theorem boundary_injective : Function.Injective boundary := by decide +kernel

/-- All coordinates lie in the stated convex clockwise polygon. -/
theorem closed_polygon_integer : ∀ v : Vertex,∀ k : Fin 9,
    orient (integerPoint (boundary k)) (integerPoint (boundary (k+1))) (integerPoint v)≤0 := by decide +kernel

/-- Nonport vertices lie strictly inside every boundary half-plane. -/
theorem inner_polygon_integer : ∀ v : Vertex,¬ IsPort v → ∀ k : Fin 9,
    orient (integerPoint (boundary k)) (integerPoint (boundary (k+1))) (integerPoint v)<0 := by decide +kernel

def closedPolygon (p : Plane) : Prop := ∀ k : Fin 9,
  realOrient (toPlane (integerPoint (boundary k))) (toPlane (integerPoint (boundary (k+1)))) p≤0

def region : Set Plane := {p | closedPolygon p ∧ p∉Set.range (drawing.point ∘ boundary)}

theorem point_in_polygon (v : Vertex) : closedPolygon (drawing.point v) := by
  intro k
  change realOrient _ _ (toPlane (integerPoint v))≤0
  rw [realOrient_cast]
  exact_mod_cast closed_polygon_integer v k

theorem port_outside_region (k : Fin 9) : drawing.point (boundary k)∉region := by
  intro h
  exact h.2 ⟨k,rfl⟩

theorem internal_in_region (v : Vertex) (hv : ¬ IsPort v) : drawing.point v∈region := by
  refine ⟨point_in_polygon v,?_⟩
  rintro ⟨k,hk⟩
  exact hv ⟨k,drawing.point_injective hk⟩

theorem curve_in_region (e : Edge) (t : I) (ht : Inside t) : drawing.curve e t∈region := by
  constructor
  · intro k
    change realOrient _ _ (affine (toPlane (integerPoint (graph.src e)))
      (toPlane (integerPoint (graph.dst e))) (t:ℝ))≤0
    rw [realOrient_affine,realOrient_cast,realOrient_cast]
    have hs : (orient (integerPoint (boundary k)) (integerPoint (boundary (k+1)))
        (integerPoint (graph.src e)):ℝ)≤0 := by exact_mod_cast closed_polygon_integer (graph.src e) k
    have hd : (orient (integerPoint (boundary k)) (integerPoint (boundary (k+1)))
        (integerPoint (graph.dst e)):ℝ)≤0 := by exact_mod_cast closed_polygon_integer (graph.dst e) k
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.2]) hs)
      (mul_nonpos_of_nonneg_of_nonpos ht.1.le hd)
  · rintro ⟨k,hk⟩
    exact drawing.interior_avoids e t ht (boundary k) hk.symm

abbrev InternalVertex := {v : Vertex // ¬ IsPort v}

def labels : (Fin 9 ⊕ InternalVertex) ≃ Vertex :=
  (Equiv.sumCongr (Equiv.ofInjective boundary boundary_injective) (Equiv.refl InternalVertex)).trans
    (Equiv.sumCompl IsPort)

def patchGraph : MultiGraph (Fin 9 ⊕ InternalVertex) Edge := graph.reindex labels.symm (Equiv.refl Edge)
def patchDrawing : PlaneDrawing patchGraph := drawing.transport (graph.reindexEquiv labels.symm (Equiv.refl Edge))

@[simp] theorem patch_port_point (k : Fin 9) : patchDrawing.point (.inl k)=drawing.point (boundary k) := rfl
@[simp] theorem patch_internal_point (v : InternalVertex) : patchDrawing.point (.inr v)=drawing.point v.val := rfl

theorem patch_internal_in_region (v : InternalVertex) : patchDrawing.point (.inr v)∈region :=
  internal_in_region v.val v.property

theorem patch_curve_in_region (e : Edge) (t : I) (ht : Inside t) : patchDrawing.curve e t∈region :=
  curve_in_region e t ht

theorem patch_port_outside_region (k : Fin 9) : patchDrawing.point (.inl k)∉region :=
  port_outside_region k

end PlanarHom.PlanarColoringClause
