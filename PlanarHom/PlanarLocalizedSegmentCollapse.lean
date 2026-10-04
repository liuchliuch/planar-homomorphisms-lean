import PlanarHom.PlanarAxialCollapse
import PlanarHom.PlaneAffineNormalization
import PlanarHom.SegmentCollapseData
import Mathlib.Topology.Order.Compact

/-!
# Localized collapse of an arbitrary plane segment

Affine conjugation transfers the explicit axial collapse to any nondegenerate
segment. Compact sets disjoint from the segment can be fixed pointwise.
-/

noncomputable section
open Set
open scoped Convex
namespace PlanarHom.MultiGraph

/-- A straight segment can be collapsed to its second endpoint by an actual
continuous plane map, fixing any prescribed disjoint compact set. The segment
is its only nonsingleton fiber, and fixed radial segments map onto themselves. -/
theorem exists_localizedSegmentCollapse {a b : Plane} {K : Set Plane}
    (hab : a ≠ b) (hK : IsCompact K) (hdis : Disjoint K [a -[ℝ] b]) :
    Nonempty (LocalizedSegmentCollapse a b K) := by
  let N := normalizeSegment a b hab
  have hmem (x : Plane) : N x ∈ [(0 : Plane) -[ℝ] (1,0)] ↔ x ∈ [a -[ℝ] b] := by
    change x ∈ (normalizeSegment a b hab) ⁻¹' [(0,0) -[ℝ] (1,0)] ↔ _
    rw [normalizeSegment_preimage, segment_symm ℝ b a]
  have hg : Continuous (fun x => AxialCollapse.gauge (N x)) :=
    AxialCollapse.continuous_gauge.comp N.continuous
  have hpos : ∀ x ∈ K, 0 < AxialCollapse.gauge (N x) := by
    intro x hx
    apply lt_of_le_of_ne (AxialCollapse.gauge_nonneg _)
    intro hz
    exact Set.disjoint_left.mp hdis hx
      ((hmem x).mp ((AxialCollapse.gauge_eq_zero_iff_mem _).mp hz.symm))
  obtain ⟨δ, hδ, hbound⟩ := hK.exists_forall_le' hg.continuousOn hpos
  let F : C(Plane,Plane) := {
    toFun x := N.symm (AxialCollapse.map δ (N x))
    continuous_toFun := N.symm.continuous.comp ((AxialCollapse.map δ).continuous.comp N.continuous) }
  have hF (x : Plane) : F x = N.symm (AxialCollapse.map δ (N x)) := rfl
  have hzero : AxialCollapse.map δ (0 : Plane) = 0 :=
    (AxialCollapse.map_eq_zero hδ _).mpr AxialCollapse.gauge_zero
  have hone : AxialCollapse.map δ (1,0) = 0 :=
    (AxialCollapse.map_eq_zero hδ _).mpr (by norm_num [AxialCollapse.gauge])
  refine ⟨{
    map := F
    fibers := ?_
    source := ?_
    target := ?_
    fixed := ?_
    ray_image := ?_ }⟩
  · intro x y
    change N.symm (AxialCollapse.map δ (N x)) = N.symm (AxialCollapse.map δ (N y)) ↔ _
    rw [N.symm.injective.eq_iff, AxialCollapse.fibers hδ, N.injective.eq_iff, hmem, hmem]
  · rw [hF]
    change N.symm (AxialCollapse.map δ (normalizeSegment a b hab a)) = b
    rw [normalizeSegment_endpoint, hone]
    exact normalizeSegment_symm_center a b hab
  · rw [hF]
    change N.symm (AxialCollapse.map δ (normalizeSegment a b hab b)) = b
    rw [normalizeSegment_center]
    change N.symm (AxialCollapse.map δ (0 : Plane)) = b
    rw [hzero]
    exact normalizeSegment_symm_center a b hab
  · intro x hx
    rw [hF, AxialCollapse.map_eq_self hδ (hbound x hx), N.symm_apply_apply]
  · intro c hc
    have hc' : AxialCollapse.map δ (N c) = N c := by
      have hh := congrArg N hc
      change N (N.symm (AxialCollapse.map δ (N c))) = N c at hh
      simpa using hh
    have hNray : N '' [b -[ℝ] c] = [(0 : Plane) -[ℝ] N c] := by
      change normalizeSegment a b hab '' [b -[ℝ] c] = _
      rw [normalizeSegment_image_segment, normalizeSegment_center]
      rfl
    calc
      F '' [b -[ℝ] c] = N.symm '' (AxialCollapse.map δ '' (N '' [b -[ℝ] c])) := by
        rw [Set.image_image, Set.image_image]
        rfl
      _ = N.symm '' [(0 : Plane) -[ℝ] N c] := by
        rw [hNray, AxialCollapse.image_ray hδ (N c) hc']
      _ = N.symm '' (N '' [b -[ℝ] c]) := by rw [hNray]
      _ = [b -[ℝ] c] := by simp [Set.image_image]

end PlanarHom.MultiGraph
