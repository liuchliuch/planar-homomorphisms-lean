import PlanarHom.SegmentCollapseData
import PlanarHom.PlaneAffineNormalization
import PlanarHom.PlanarSlitOpening

/-!
# Normalizing a straight complementary slit

A straight segment whose only contacts with a drawing are its two endpoints
can be affinely normalized to the horizontal unit segment. The transformed
ordinary drawing therefore supplies the domain needed for slit opening.
-/

noncomputable section
open Set
open scoped Convex
namespace PlanarHom.MultiGraph.PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Normalize the endpoints of a straight slit while preserving the ordinary
drawing and exclusion of the slit interior. -/
theorem exists_normalizedSlitDrawing (d : PlaneDrawing G) {u v : V} (huv : u ≠ v)
    (hcontact : ∀ w, w ∈ [d.point u -[ℝ] d.point v] → w ∈ d.support →
      w = d.point u ∨ w = d.point v) :
    ∃ D : PlaneDrawing G, D.AvoidsOpenUnitSegment ∧
      D.point u = (0,0) ∧ D.point v = (1,0) := by
  let hab := d.point_injective.ne huv.symm
  let N := normalizeSegment (d.point v) (d.point u) hab
  let F : C(Plane,Plane) := ⟨N,N.continuous⟩
  let D := d.mapOnSupport F N.injective.injOn
  have hleft : D.point u = (0,0) := normalizeSegment_center _ _ hab
  have hright : D.point v = (1,0) := normalizeSegment_endpoint _ _ hab
  refine ⟨D,?_,hleft,hright⟩
  intro p hp hopen
  have hsupport : p ∈ N '' d.support := by
    change p ∈ (d.mapOnSupport F N.injective.injOn).support at hp
    rw [d.support_mapOnSupport] at hp
    exact hp
  obtain ⟨w,hw,rfl⟩ := hsupport
  have haxis : N w ∈ [(0,0) -[ℝ] (1,0)] := by
    rw [segment_eq_image_lineMap]
    refine ⟨(N w).1,⟨hopen.1.le,hopen.2.1.le⟩,?_⟩
    apply Prod.ext <;> simp [AffineMap.lineMap_apply_module,hopen.2.2]
  have hsegment : w ∈ [d.point u -[ℝ] d.point v] := by
    rw [← normalizeSegment_preimage (d.point v) (d.point u) hab]
    exact haxis
  rcases hcontact w hsegment hw with h | h
  · have hz : N w = (0,0) := h ▸ normalizeSegment_center _ _ hab
    rw [hz] at hopen
    exact (lt_irrefl 0) hopen.1
  · have hz : N w = (1,0) := h ▸ normalizeSegment_endpoint _ _ hab
    rw [hz] at hopen
    exact (lt_irrefl 1) hopen.2.1

end PlanarHom.MultiGraph.PlaneDrawing
