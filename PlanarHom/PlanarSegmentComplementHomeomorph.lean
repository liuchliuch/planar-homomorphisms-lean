import PlanarHom.PlanarAxialCollapse
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Homeomorph.Defs

/-!
# NEW actual homeomorphism after collapsing a straight tree segment

The baseline provides an explicit continuous axial collapse and exact fibers.
Here we prove it is onto and proper from its formula. Its restriction away from
the collapsed segment is therefore an actual homeomorphism to the punctured plane.
No ambient isotopy or tree-cut chart is assumed.
-/
noncomputable section
open Set Topology Filter
open scoped Convex
namespace PlanarHom.MultiGraph.AxialCollapse

/-- The explicit collapse gauge controls distance to infinity. -/
theorem norm_le_gauge_add_one (p : Plane) : ‖p‖ ≤ gauge p + 1 := by
  rw [Prod.norm_def, max_le_iff]
  have h₁ := le_max_right 0 (p.1-1)
  have h₂ := le_max_right 0 (-p.1)
  have hz₁ := le_max_left 0 (p.1-1)
  have hz₂ := le_max_left 0 (-p.1)
  simp only [Real.norm_eq_abs]
  constructor
  · by_cases hp : 0 ≤ p.1
    · rw [abs_of_nonneg hp]
      dsimp [gauge]
      linarith [abs_nonneg p.2]
    · rw [abs_of_neg (lt_of_not_ge hp)]
      dsimp [gauge]
      linarith [abs_nonneg p.2]
  · dsimp [gauge]
    linarith

/-- Outside a concrete closed ball the actual formula is exactly the identity. -/
theorem map_eq_self_of_norm {δ : ℝ} (hδ : 0 < δ) {p : Plane}
    (hp : δ+1 ≤ ‖p‖) : map δ p = p := by
  apply map_eq_self hδ
  linarith [norm_le_gauge_add_one p]

/-- Every point is reached by the explicit segment collapse. -/
theorem map_surjective {δ : ℝ} (hδ : 0 < δ) : Function.Surjective (map δ) := by
  intro y
  by_cases hy : y = 0
  · subst y
    exact ⟨0,(map_eq_zero hδ 0).mpr gauge_zero⟩
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let r := (δ+1)/‖y‖+1
  have hr : 1 ≤ r := by
    dsimp [r]
    have := div_nonneg (by linarith : 0 ≤ δ+1) hn.le
    linarith
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlarge : δ+1 ≤ ‖r • y‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr0]
    dsimp [r]
    rw [add_mul,div_mul_cancel₀ _ hn.ne']
    linarith
  have hfix := map_eq_self_of_norm hδ hlarge
  have hymem : y ∈ [(0:Plane) -[ℝ] r • y] := by
    rw [segment_eq_image_lineMap]
    refine ⟨r⁻¹,⟨inv_nonneg.mpr hr0.le,(inv_le_one₀ hr0).mpr hr⟩,?_⟩
    simp [AffineMap.lineMap_apply_module,smul_smul,hr0.ne']
  rw [← image_ray hδ (r • y) hfix] at hymem
  obtain ⟨x,_,hx⟩ := hymem
  exact ⟨x,hx⟩

/-- The explicit map is proper because it equals the identity outside a compact
ball. This is proved, rather than included in a collapse certificate. -/
theorem map_isProperMap {δ : ℝ} (hδ : 0 < δ) : IsProperMap (map δ) := by
  apply isProperMap_iff_tendsto_cocompact.mpr
  refine ⟨(map δ).continuous,?_⟩
  have heq : (map δ : Plane → Plane) =ᶠ[cocompact Plane] id := by
    filter_upwards [(isCompact_closedBall (0:Plane) (δ+1)).compl_mem_cocompact] with p hp
    apply map_eq_self_of_norm hδ
    simp only [Set.mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le] at hp
    exact hp.le
  exact tendsto_id.congr' heq.symm

/-- The map is closed on the entire plane. -/
theorem map_isClosedMap {δ : ℝ} (hδ : 0 < δ) : IsClosedMap (map δ) :=
  (map_isProperMap hδ).isClosedMap

/-- Restrict the proved proper surjection to the complement of its exceptional
fiber. Its inverse is continuous because the restriction is a closed bijection. -/
def preimageComplementHomeomorph {δ : ℝ} (hδ : 0 < δ) :
    {x : Plane // map δ x ≠ 0} ≃ₜ {y : Plane // y ≠ 0} := by
  let S : Set Plane := {y | y ≠ 0}
  let f := S.restrictPreimage (map δ)
  have hinj : Function.Injective f := by
    intro x y h
    have hh : map δ x.val = map δ y.val := congrArg Subtype.val h
    rcases (fibers hδ x.val y.val).mp hh with heq | hseg
    · exact Subtype.ext heq
    · exact False.elim (x.property ((map_eq_zero hδ x.val).mpr
        ((gauge_eq_zero_iff_mem x.val).mpr hseg.1)))
  have hsur : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := map_surjective hδ y.val
    refine ⟨⟨x,?_⟩,Subtype.ext hx⟩
    change map δ x ≠ 0
    rw [hx]
    exact y.property
  exact (Equiv.ofBijective f ⟨hinj,hsur⟩).toHomeomorphOfContinuousClosed
    (map δ).continuous.restrictPreimage ((map_isClosedMap hδ).restrictPreimage S)

/-- Actual complement homeomorphism for the concrete closed unit segment. -/
def complementHomeomorph {δ : ℝ} (hδ : 0 < δ) :
    {x : Plane // x ∉ [(0:Plane) -[ℝ] (1,0)]} ≃ₜ {y : Plane // y ≠ 0} := by
  have heq : {x : Plane | x ∉ [(0:Plane) -[ℝ] (1,0)]} = {x | map δ x ≠ 0} := by
    ext x
    exact (not_congr ((map_eq_zero hδ x).trans (gauge_eq_zero_iff_mem x))).symm
  exact (Homeomorph.setCongr heq).trans (preimageComplementHomeomorph hδ)

@[simp] theorem complementHomeomorph_apply {δ : ℝ} (hδ : 0 < δ)
    (x : {x : Plane // x ∉ [(0:Plane) -[ℝ] (1,0)]}) :
    ((complementHomeomorph hδ x : {y : Plane // y ≠ 0}) : Plane) = map δ x := rfl

end PlanarHom.MultiGraph.AxialCollapse
