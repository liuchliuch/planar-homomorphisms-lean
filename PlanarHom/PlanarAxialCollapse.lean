import PlanarHom.PlanarEdgeOperations
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# An explicit collapse of a straight segment

The map constructed here has exactly one nonsingleton fiber, the horizontal
unit segment. Its support can be confined to an arbitrarily thin neighborhood
of that segment. Every ray from the left endpoint is preserved.
-/

noncomputable section
open Set
open scoped Convex
namespace PlanarHom.MultiGraph.AxialCollapse

/-- A piecewise linear nonnegative function vanishing precisely on the unit segment. -/
def gauge (p : Plane) : ℝ := max 0 (p.1 - 1) + max 0 (-p.1) + |p.2|

theorem gauge_nonneg (p : Plane) : 0 ≤ gauge p := by
  unfold gauge
  positivity

theorem continuous_gauge : Continuous gauge := by unfold gauge; fun_prop

theorem gauge_eq_zero (p : Plane) :
    gauge p = 0 ↔ 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0 := by
  constructor
  · intro h
    have h₁ : 0 ≤ max 0 (p.1 - 1) := le_max_left _ _
    have h₂ : 0 ≤ max 0 (-p.1) := le_max_left _ _
    have h₃ := abs_nonneg p.2
    have hx := le_max_right 0 (p.1 - 1)
    have hy := le_max_right 0 (-p.1)
    have hz : |p.2| = 0 := by unfold gauge at h; linarith
    refine ⟨?_, ?_, abs_eq_zero.mp hz⟩ <;> unfold gauge at h <;> linarith
  · rintro ⟨hx, hy, hz⟩
    simp [gauge, max_eq_left (sub_nonpos.mpr hy), max_eq_left (neg_nonpos.mpr hx), hz]

theorem mem_unitSegment (p : Plane) :
    p ∈ [(0 : Plane) -[ℝ] (1, 0)] ↔ 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0 := by
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa [AffineMap.lineMap_apply_module] using And.intro ht.1 (And.intro ht.2 (rfl : (0 : ℝ) = 0))
  · rintro ⟨hx, hy, hz⟩
    refine ⟨p.1, ⟨hx, hy⟩, ?_⟩
    apply Prod.ext <;> simp [AffineMap.lineMap_apply_module, hz]

theorem gauge_eq_zero_iff_mem (p : Plane) :
    gauge p = 0 ↔ p ∈ [(0 : Plane) -[ℝ] (1, 0)] :=
  (gauge_eq_zero p).trans (mem_unitSegment p).symm

@[simp] theorem gauge_zero : gauge 0 = 0 := by simp [gauge]

theorem gauge_smul_mono {p : Plane} {r : ℝ} (hr : 1 ≤ r) :
    gauge p ≤ gauge (r • p) := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hy : |p.2| ≤ |r * p.2| := by
    rw [abs_mul, abs_of_nonneg hr0]
    nlinarith [abs_nonneg p.2]
  change max 0 (p.1 - 1) + max 0 (-p.1) + |p.2| ≤
    max 0 (r * p.1 - 1) + max 0 (-(r * p.1)) + |r * p.2|
  by_cases hx : 0 ≤ p.1
  · have hxr : 0 ≤ r * p.1 := mul_nonneg hr0 hx
    rw [max_eq_left (neg_nonpos.mpr hx), max_eq_left (neg_nonpos.mpr hxr)]
    have hm : max 0 (p.1 - 1) ≤ max 0 (r * p.1 - 1) := by
      apply max_le_max le_rfl
      nlinarith
    linarith
  · have hx0 : p.1 ≤ 0 := le_of_not_ge hx
    have hxr : r * p.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 hx0
    rw [max_eq_left (by linarith : p.1 - 1 ≤ 0),
      max_eq_left (by linarith : r * p.1 - 1 ≤ 0),
      max_eq_right (neg_nonneg.mpr hx0), max_eq_right (neg_nonneg.mpr hxr)]
    nlinarith

def factor (δ : ℝ) (p : Plane) : ℝ := min 1 (gauge p / δ)

theorem continuous_factor (δ : ℝ) : Continuous (factor δ) := by
  unfold factor
  exact continuous_const.min (continuous_gauge.div_const δ)

theorem factor_nonneg {δ : ℝ} (hδ : 0 < δ) (p : Plane) : 0 ≤ factor δ p :=
  le_min zero_le_one (div_nonneg (gauge_nonneg p) hδ.le)

theorem factor_le_one (δ : ℝ) (p : Plane) : factor δ p ≤ 1 := min_le_left _ _

theorem factor_pos {δ : ℝ} (hδ : 0 < δ) {p : Plane} (hp : gauge p ≠ 0) :
    0 < factor δ p :=
  lt_min zero_lt_one (div_pos (lt_of_le_of_ne (gauge_nonneg p) (Ne.symm hp)) hδ)

theorem factor_eq_zero {δ : ℝ} (hδ : 0 < δ) (p : Plane) :
    factor δ p = 0 ↔ gauge p = 0 := by
  constructor
  · intro h
    by_contra hp
    exact (factor_pos hδ hp).ne' h
  · intro h
    simp [factor, h]

theorem factor_eq_one {δ : ℝ} (hδ : 0 < δ) {p : Plane} (hp : δ ≤ gauge p) :
    factor δ p = 1 := min_eq_left ((le_div_iff₀ hδ).mpr (by simpa using hp))

theorem factor_smul_mono {δ : ℝ} (hδ : 0 < δ) {p : Plane} {r : ℝ} (hr : 1 ≤ r) :
    factor δ p ≤ factor δ (r • p) :=
  min_le_min le_rfl (div_le_div_of_nonneg_right (gauge_smul_mono hr) hδ.le)

/-- The actual continuous radial collapse. -/
def map (δ : ℝ) : C(Plane, Plane) where
  toFun p := factor δ p • p
  continuous_toFun := (continuous_factor δ).smul continuous_id

theorem map_eq_zero {δ : ℝ} (hδ : 0 < δ) (p : Plane) :
    map δ p = 0 ↔ gauge p = 0 := by
  change factor δ p • p = 0 ↔ _
  rw [smul_eq_zero]
  constructor
  · rintro (h | rfl)
    · exact (factor_eq_zero hδ p).mp h
    · exact gauge_zero
  · intro h
    exact Or.inl ((factor_eq_zero hδ p).mpr h)

theorem map_eq_self {δ : ℝ} (hδ : 0 < δ) {p : Plane} (hp : δ ≤ gauge p) :
    map δ p = p := by simp [map, factor_eq_one hδ hp]

theorem fibers {δ : ℝ} (hδ : 0 < δ) (p q : Plane) :
    map δ p = map δ q ↔ p = q ∨
      (p ∈ [(0 : Plane) -[ℝ] (1,0)] ∧ q ∈ [(0 : Plane) -[ℝ] (1,0)]) := by
  constructor
  · intro h
    by_cases hp : gauge p = 0
    · have hq : gauge q = 0 := (map_eq_zero hδ q).mp (h.symm.trans ((map_eq_zero hδ p).mpr hp))
      exact Or.inr ⟨(gauge_eq_zero_iff_mem p).mp hp, (gauge_eq_zero_iff_mem q).mp hq⟩
    have hq : gauge q ≠ 0 := by
      intro hq
      exact hp ((map_eq_zero hδ p).mp (h.trans ((map_eq_zero hδ q).mpr hq)))
    have hap : 0 < factor δ p := factor_pos hδ hp
    have haq : 0 < factor δ q := factor_pos hδ hq
    have hp0 : p ≠ 0 := by intro he; exact hp (he ▸ gauge_zero)
    have hq0 : q ≠ 0 := by intro he; exact hq (he ▸ gauge_zero)
    have eq_of_le (hle : factor δ p ≤ factor δ q) : p = q := by
      have hr : 1 ≤ factor δ q / factor δ p := (le_div_iff₀ hap).mpr (by simpa using hle)
      have he : p = (factor δ q / factor δ p) • q := by
        have hh := congrArg (fun z : Plane => (factor δ p)⁻¹ • z) h
        change (factor δ p)⁻¹ • (factor δ p • p) =
          (factor δ p)⁻¹ • (factor δ q • q) at hh
        simpa [smul_smul, inv_mul_cancel₀ hap.ne', div_eq_inv_mul] using hh
      have hm : factor δ q ≤ factor δ p := by
        simpa only [← he] using factor_smul_mono hδ (p := q) hr
      have hf : factor δ p = factor δ q := le_antisymm hle hm
      change factor δ p • p = factor δ q • q at h
      rw [← hf] at h
      exact (smul_right_injective _ hap.ne') h
    by_cases hle : factor δ p ≤ factor δ q
    · exact Or.inl (eq_of_le hle)
    · have hle' : factor δ q ≤ factor δ p := le_of_not_ge hle
      have hr : 1 ≤ factor δ p / factor δ q := (le_div_iff₀ haq).mpr (by simpa using hle')
      have he : q = (factor δ p / factor δ q) • p := by
        have hh := congrArg (fun z : Plane => (factor δ q)⁻¹ • z) h.symm
        change (factor δ q)⁻¹ • (factor δ q • q) =
          (factor δ q)⁻¹ • (factor δ p • p) at hh
        simpa [smul_smul, inv_mul_cancel₀ haq.ne', div_eq_inv_mul] using hh
      have hm : factor δ p ≤ factor δ q := by
        simpa only [← he] using factor_smul_mono hδ (p := p) hr
      exact Or.inl (eq_of_le hm)
  · rintro (rfl | ⟨hp, hq⟩)
    · rfl
    · rw [(map_eq_zero hδ p).mpr ((gauge_eq_zero_iff_mem p).mpr hp),
        (map_eq_zero hδ q).mpr ((gauge_eq_zero_iff_mem q).mpr hq)]

theorem image_ray_subset {δ : ℝ} (hδ : 0 < δ) (c : Plane) :
    map δ '' [(0 : Plane) -[ℝ] c] ⊆ [(0 : Plane) -[ℝ] c] := by
  rintro x ⟨p, hp, rfl⟩
  rw [segment_eq_image_lineMap] at hp ⊢
  obtain ⟨t, ht, rfl⟩ := hp
  refine ⟨factor δ (t • c) * t, ⟨mul_nonneg (factor_nonneg hδ _) ht.1, ?_⟩, ?_⟩
  · exact mul_le_one₀ (factor_le_one _ _) ht.1 ht.2
  · simp [map, AffineMap.lineMap_apply_module, smul_smul]

theorem image_ray {δ : ℝ} (hδ : 0 < δ) (c : Plane) (hc : map δ c = c) :
    map δ '' [(0 : Plane) -[ℝ] c] = [(0 : Plane) -[ℝ] c] := by
  apply Subset.antisymm (image_ray_subset hδ c)
  by_cases hc0 : c = 0
  · subst c
    simp only [segment_same, image_singleton]
    have hzero : map δ 0 = 0 := (map_eq_zero hδ 0).mpr gauge_zero
    simp [hzero]
  have hf1 : factor δ c = 1 := by
    apply (smul_left_injective ℝ hc0)
    simpa only [one_smul] using hc
  let f : ℝ → ℝ := fun t => factor δ (t • c) * t
  have hcont : Continuous f := ((continuous_factor δ).comp (continuous_id.smul continuous_const)).mul continuous_id
  have hf0 : f 0 = 0 := by simp [f]
  have hf1' : f 1 = 1 := by simp [f, hf1]
  intro x hx
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have hft : t ∈ Set.Icc (f 0) (f 1) := by simpa only [hf0, hf1'] using ht
  obtain ⟨s, hs, hst⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn hft
  refine ⟨s • c, ?_, ?_⟩
  · rw [segment_eq_image_lineMap]
    refine ⟨s, hs, ?_⟩
    simp [AffineMap.lineMap_apply_module]
  · change factor δ (s • c) • (s • c) = _
    rw [smul_smul]
    change f s • c = _
    rw [hst]
    simp [AffineMap.lineMap_apply_module]

end PlanarHom.MultiGraph.AxialCollapse
