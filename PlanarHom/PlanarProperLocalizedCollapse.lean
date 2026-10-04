import PlanarHom.PlanarSegmentComplementHomeomorph
import PlanarHom.PlanarLocalizedSegmentCollapse
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# NEW proper localized segment collapse and its exact ambient complement map

Affine conjugation transfers the proved explicit axial collapse to any segment.
A common positive scale is chosen from actual compact separation. The result
supplies the existing localized-collapse API together with proved surjectivity,
properness, and a complement homeomorphism whose forward map is the same formula.
-/
noncomputable section
open Set Topology
open scoped Convex
namespace PlanarHom.MultiGraph.SegmentCollapse

variable (a b : Plane) (hab : a ≠ b)

def map (δ : ℝ) : C(Plane,Plane) where
  toFun x := (normalizeSegment a b hab).symm (AxialCollapse.map δ (normalizeSegment a b hab x))
  continuous_toFun := (normalizeSegment a b hab).symm.continuous.comp
    ((AxialCollapse.map δ).continuous.comp (normalizeSegment a b hab).continuous)

theorem normalized_mem (x : Plane) :
    normalizeSegment a b hab x ∈ [(0:Plane) -[ℝ] (1,0)] ↔ x ∈ [a -[ℝ] b] := by
  change x ∈ normalizeSegment a b hab ⁻¹' [(0,0) -[ℝ] (1,0)] ↔ _
  rw [normalizeSegment_preimage,segment_symm ℝ b a]

theorem map_fibers {δ : ℝ} (hδ : 0 < δ) (x y : Plane) :
    map a b hab δ x = map a b hab δ y ↔ x=y ∨ (x∈[a -[ℝ] b] ∧ y∈[a -[ℝ] b]) := by
  change (normalizeSegment a b hab).symm _ = (normalizeSegment a b hab).symm _ ↔ _
  rw [(normalizeSegment a b hab).symm.injective.eq_iff,AxialCollapse.fibers hδ,
    (normalizeSegment a b hab).injective.eq_iff,normalized_mem,normalized_mem]

theorem map_isProperMap {δ : ℝ} (hδ : 0 < δ) : IsProperMap (map a b hab δ) :=
  (normalizeSegment a b hab).symm.isProperMap.comp
    ((AxialCollapse.map_isProperMap hδ).comp (normalizeSegment a b hab).isProperMap)

theorem map_surjective {δ : ℝ} (hδ : 0 < δ) : Function.Surjective (map a b hab δ) :=
  (normalizeSegment a b hab).symm.surjective.comp
    ((AxialCollapse.map_surjective hδ).comp (normalizeSegment a b hab).surjective)

/-- The ambient map off the original segment, with both endpoints removed. -/
def complementHomeomorph {δ : ℝ} (hδ : 0 < δ) :
    {x : Plane // x ∉ [a -[ℝ] b]} ≃ₜ {y : Plane // y ≠ b} :=
  ((normalizeSegment a b hab).subtype (fun x => (not_congr (normalized_mem a b hab x)).symm)).trans
    ((AxialCollapse.complementHomeomorph hδ).trans
      ((normalizeSegment a b hab).symm.subtype (fun y => by
        calc
          y ≠ 0 ↔ (normalizeSegment a b hab).symm y ≠ (normalizeSegment a b hab).symm 0 :=
            not_congr (normalizeSegment a b hab).symm.injective.eq_iff.symm
          _ ↔ (normalizeSegment a b hab).symm y ≠ b := by
            have hz : (normalizeSegment a b hab).symm (0:Plane) = b := normalizeSegment_symm_center a b hab
            rw [hz])))

@[simp] theorem complementHomeomorph_apply {δ : ℝ} (hδ : 0 < δ)
    (x : {x : Plane // x ∉ [a -[ℝ] b]}) :
    ((complementHomeomorph a b hab hδ x : {y : Plane // y ≠ b}) : Plane) =
      map a b hab δ x := rfl

theorem map_source {δ : ℝ} (hδ : 0 < δ) : map a b hab δ a = b := by
  change (normalizeSegment a b hab).symm (AxialCollapse.map δ (normalizeSegment a b hab a)) = b
  rw [normalizeSegment_endpoint,
    (AxialCollapse.map_eq_zero hδ _).mpr (by norm_num [AxialCollapse.gauge])]
  exact normalizeSegment_symm_center a b hab

theorem map_target {δ : ℝ} (hδ : 0 < δ) : map a b hab δ b = b := by
  change (normalizeSegment a b hab).symm (AxialCollapse.map δ (normalizeSegment a b hab b)) = b
  rw [normalizeSegment_center]
  change (normalizeSegment a b hab).symm (AxialCollapse.map δ (0:Plane)) = b
  rw [(AxialCollapse.map_eq_zero hδ _).mpr AxialCollapse.gauge_zero]
  exact normalizeSegment_symm_center a b hab

/-- Actual compact clearance supplies a single positive collapse scale fixing
all selected points, rather than a supplied properness or inverse certificate. -/
theorem exists_fixed_scale {K : Set Plane} (hK : IsCompact K)
    (hdis : Disjoint K [a -[ℝ] b]) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x∈K, map a b hab δ x = x := by
  have hg : Continuous (fun x => AxialCollapse.gauge (normalizeSegment a b hab x)) :=
    AxialCollapse.continuous_gauge.comp (normalizeSegment a b hab).continuous
  have hpos : ∀ x∈K, 0 < AxialCollapse.gauge (normalizeSegment a b hab x) := by
    intro x hx
    apply lt_of_le_of_ne (AxialCollapse.gauge_nonneg _)
    intro hz
    exact Set.disjoint_left.mp hdis hx ((normalized_mem a b hab x).mp
      ((AxialCollapse.gauge_eq_zero_iff_mem _).mp hz.symm))
  obtain ⟨δ,hδ,hbound⟩ := hK.exists_forall_le' hg.continuousOn hpos
  refine ⟨δ,hδ,fun x hx => ?_⟩
  change (normalizeSegment a b hab).symm (AxialCollapse.map δ (normalizeSegment a b hab x)) = x
  rw [AxialCollapse.map_eq_self hδ (hbound x hx),(normalizeSegment a b hab).symm_apply_apply]

/-- Fixed rays at the contraction center retain their full actual image. -/
theorem map_ray_image {δ : ℝ} (hδ : 0 < δ) (c : Plane) (hc : map a b hab δ c = c) :
    map a b hab δ '' [b -[ℝ] c] = [b -[ℝ] c] := by
  let N := normalizeSegment a b hab
  have hc' : AxialCollapse.map δ (N c) = N c := by
    have hh := congrArg N hc
    change N (N.symm (AxialCollapse.map δ (N c))) = N c at hh
    simpa using hh
  have hray : N '' [b -[ℝ] c] = [(0:Plane) -[ℝ] N c] := by
    change normalizeSegment a b hab '' [b -[ℝ] c] = _
    rw [normalizeSegment_image_segment,normalizeSegment_center]
    rfl
  calc
    map a b hab δ '' [b -[ℝ] c] = N.symm '' (AxialCollapse.map δ '' (N '' [b -[ℝ] c])) := by
      rw [Set.image_image,Set.image_image]
      rfl
    _ = N.symm '' [(0:Plane) -[ℝ] N c] := by rw [hray,AxialCollapse.image_ray hδ _ hc']
    _ = N.symm '' (N '' [b -[ℝ] c]) := by rw [hray]
    _ = [b -[ℝ] c] := by simp [Set.image_image]

include hab in
/-- Existing localized-collapse data, now accompanied by proved global topology. -/
theorem exists_properLocalizedSegmentCollapse {K : Set Plane} (hK : IsCompact K)
    (hdis : Disjoint K [a -[ℝ] b]) :
    ∃ C : LocalizedSegmentCollapse a b K,
      IsProperMap C.map ∧ Function.Surjective C.map ∧
      ∃ H : {x : Plane // x ∉ [a -[ℝ] b]} ≃ₜ {y : Plane // y ≠ b},
        ∀ x, (H x : Plane) = C.map x := by
  obtain ⟨δ,hδ,hfix⟩ := exists_fixed_scale a b hab hK hdis
  let C : LocalizedSegmentCollapse a b K := {
    map := map a b hab δ
    fibers := map_fibers a b hab hδ
    source := map_source a b hab hδ
    target := map_target a b hab hδ
    fixed := hfix
    ray_image := map_ray_image a b hab hδ }
  exact ⟨C,map_isProperMap a b hab hδ,map_surjective a b hab hδ,
    complementHomeomorph a b hab hδ,fun _ => rfl⟩

end PlanarHom.MultiGraph.SegmentCollapse
