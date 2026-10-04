import PlanarHom.PlanarEmbedding
import Mathlib.Analysis.Convex.Topology

/-!
# Exact local segment-collapse data and retained drawings

The data records a concrete continuous plane map, its exact fibers, its fixed
compact set and its action on rays. Existence is supplied by the explicit axial
construction. Restricting an injective map to an actual drawing's support
preserves every ordinary plane-drawing condition.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.MultiGraph

/-- A local collapse of one segment toward its second endpoint, preserving
chosen points and every radial segment whose far endpoint is fixed. -/
structure LocalizedSegmentCollapse (a b : Plane) (K : Set Plane) where
  map : C(Plane,Plane)
  fibers : ∀ x y, map x = map y ↔ x = y ∨
    (x ∈ [a -[ℝ] b] ∧ y ∈ [a -[ℝ] b])
  source : map a = b
  target : map b = b
  fixed : ∀ x ∈ K, map x = x
  ray_image : ∀ c, map c = c → map '' [b -[ℝ] c] = [b -[ℝ] c]

namespace PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Apply a continuous plane map that is injective on the complete drawn graph. -/
def mapOnSupport (d : PlaneDrawing G) (F : C(Plane,Plane))
    (hF : Set.InjOn F d.support) : PlaneDrawing G where
  point v := F (d.point v)
  point_injective := by
    intro v w h
    apply d.point_injective
    exact hF (Or.inl ⟨v,rfl⟩) (Or.inl ⟨w,rfl⟩) h
  curve e := F.comp (d.curve e)
  curve_zero e := congrArg F (d.curve_zero e)
  curve_one e := congrArg F (d.curve_one e)
  interior_injective := by
    intro e f s t hs ht h
    apply d.interior_injective e f s t hs ht
    exact hF (Or.inr (Set.mem_iUnion.mpr ⟨e,s,rfl⟩))
      (Or.inr (Set.mem_iUnion.mpr ⟨f,t,rfl⟩)) h
  interior_avoids := by
    intro e t ht v h
    apply d.interior_avoids e t ht v
    exact hF (Or.inr (Set.mem_iUnion.mpr ⟨e,t,rfl⟩)) (Or.inl ⟨v,rfl⟩) h

/-- The transformed support is precisely the image of the original support. -/
theorem support_mapOnSupport (d : PlaneDrawing G) (F : C(Plane,Plane))
    (hF : Set.InjOn F d.support) : (d.mapOnSupport F hF).support = F '' d.support := by
  ext x
  constructor
  · rintro (⟨v,rfl⟩ | hx)
    · exact ⟨d.point v,Or.inl ⟨v,rfl⟩,rfl⟩
    · obtain ⟨e,t,rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨d.curve e t,Or.inr (Set.mem_iUnion.mpr ⟨e,t,rfl⟩),rfl⟩
  · rintro ⟨y,(⟨v,rfl⟩ | hy),rfl⟩
    · exact Or.inl ⟨v,rfl⟩
    · obtain ⟨e,t,rfl⟩ := Set.mem_iUnion.mp hy
      exact Or.inr (Set.mem_iUnion.mpr ⟨e,t,rfl⟩)

end PlaneDrawing
end PlanarHom.MultiGraph
