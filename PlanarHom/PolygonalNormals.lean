import PlanarHom.PolygonalStrips

/-!
# Transverse directions and small embedded polygonal strips

Nonopposite consecutive edge directions admit a common positive transverse
vector. The finite corner signs needed for actual bilinear strip injectivity
then hold for every sufficiently small positive width.
-/

noncomputable section
open Set unitInterval Filter
open scoped Topology Convex
namespace PlanarHom.Polygonal
open MultiGraph

/-- Counterclockwise quarter turn in the actual plane. -/
def rotate (v : Plane) : Plane := (-v.2, v.1)

@[simp] theorem cross_rotate (v : Plane) : cross v (rotate v) = v.1 ^ 2 + v.2 ^ 2 := by
  simp [cross, rotate]
  ring

theorem cross_rotate_pos (v : Plane) (hv : v ≠ 0) : 0 < cross v (rotate v) := by
  rw [cross_rotate]
  have hcoord : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hv (Prod.ext hn.1 hn.2)
  rcases hcoord with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg v.2]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg v.1]

/-- Vanishing planar determinant gives an actual scalar multiple. -/
theorem exists_smul_of_cross_eq_zero (v w : Plane) (hv : v ≠ 0) (h : cross v w = 0) :
    ∃ k : ℝ, w = k • v := by
  by_cases hv1 : v.1 = 0
  · have hv2 : v.2 ≠ 0 := by
      intro hz
      exact hv (Prod.ext hv1 hz)
    have hw1 : w.1 = 0 := by
      have hm : v.2 * w.1 = 0 := by simpa [cross, hv1] using h
      exact (mul_eq_zero.mp hm).resolve_left hv2
    refine ⟨w.2 / v.2, ?_⟩
    apply Prod.ext
    · simp [Prod.smul_fst, hv1, hw1]
    · simp [Prod.smul_snd, div_mul_cancel₀ _ hv2]
  · refine ⟨w.1 / v.1, ?_⟩
    apply Prod.ext
    · simp [Prod.smul_fst, div_mul_cancel₀ _ hv1]
    · change w.2 = w.1 / v.1 * v.2
      field_simp
      dsimp [cross] at h
      nlinarith

/-- Consecutive directions which do not reverse along the same ray have a
single transverse vector positive for both directions. -/
theorem exists_common_transverse (v w : Plane) (hv : v ≠ 0) (hw : w ≠ 0)
    (hnot : ¬ ∃ c : ℝ, 0 < c ∧ w = (-c) • v) :
    ∃ N : Plane, 0 < cross v N ∧ 0 < cross w N := by
  by_cases hdet : cross v w = 0
  · obtain ⟨k, hk⟩ := exists_smul_of_cross_eq_zero v w hv hdet
    have hk0 : k ≠ 0 := by
      intro he
      apply hw
      simpa [he] using hk
    have hkpos : 0 < k := by
      by_contra hn
      have hkneg : k < 0 := lt_of_le_of_ne (le_of_not_gt hn) hk0
      exact hnot ⟨-k, neg_pos.mpr hkneg, by simpa using hk⟩
    refine ⟨rotate v, cross_rotate_pos v hv, ?_⟩
    rw [hk, cross_smul_left]
    exact mul_pos hkpos (cross_rotate_pos v hv)
  · refine ⟨(cross v w)⁻¹ • (w - v), ?_, ?_⟩
    · simp [cross_smul_right, hdet]
    · rw [cross_smul_right, cross_sub_right, cross_self, cross_swap w v]
      simpa [hdet] using (show (0 : ℝ) < 1 by norm_num)

/-- Small positive widths give the actual four-corner determinant conditions
for two nonpinched transverse cross-sections. -/
theorem eventually_corner_positive (P Q A B : Plane)
    (hA : 0 < cross (Q - P) A) (hB : 0 < cross (Q - P) B) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0,
      0 < cross (Q - P) (ε • A) ∧ 0 < cross (Q - P) (ε • B) ∧
      0 < cross (Q - P + (ε • B - ε • A)) (ε • A) ∧
      0 < cross (Q - P + (ε • B - ε • A)) (ε • B) := by
  have hlimA : Tendsto (fun ε : ℝ => cross (Q - P + ε • (B - A)) A) (𝓝 0)
      (𝓝 (cross (Q - P) A)) := by
    have hc : Continuous (fun ε : ℝ => cross (Q - P + ε • (B - A)) A) := by
      unfold cross
      fun_prop
    simpa using hc.continuousAt.tendsto (x := (0 : ℝ))
  have hlimB : Tendsto (fun ε : ℝ => cross (Q - P + ε • (B - A)) B) (𝓝 0)
      (𝓝 (cross (Q - P) B)) := by
    have hc : Continuous (fun ε : ℝ => cross (Q - P + ε • (B - A)) B) := by
      unfold cross
      fun_prop
    simpa using hc.continuousAt.tendsto (x := (0 : ℝ))
  have ha := (hlimA.eventually_const_lt hA).filter_mono
    (show 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hb := (hlimB.eventually_const_lt hB).filter_mono
    (show 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0 from nhdsWithin_le_nhds)
  filter_upwards [ha, hb, self_mem_nhdsWithin] with ε ha hb hε
  have hpos : 0 < ε := hε
  refine ⟨by simpa using mul_pos hpos hA, by simpa using mul_pos hpos hB, ?_, ?_⟩
  · simpa only [← smul_sub, cross_smul_right] using mul_pos hpos ha
  · simpa only [← smul_sub, cross_smul_right] using mul_pos hpos hb

/-- The whole closed-square strip is genuinely embedded away from its endpoint
sides for all sufficiently small positive widths. -/
theorem eventually_stripMap_injective (P Q A B : Plane)
    (hA : 0 < cross (Q - P) A) (hB : 0 < cross (Q - P) B) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, ∀ p q : I × I,
      Inside p.1 → Inside q.1 →
      stripMap P Q (ε • A) (ε • B) p = stripMap P Q (ε • A) (ε • B) q → p = q := by
  filter_upwards [eventually_corner_positive P Q A B hA hB] with ε hε
  intro p q hp hq heq
  exact stripMap_injective_of_corner_signs P Q (ε • A) (ε • B)
    hε.1.le hε.2.1.le hε.2.2.1.le hε.2.2.2.le
    (Or.inl hε.1) (Or.inl hε.2.2.1) p q hp hq heq


/-- A genuine nonoverlapping polygonal corner cannot reverse along the same ray. -/
theorem not_opposite_of_segment_intersection (P Q R : Plane) (hPQ : P ≠ Q)
    (hinter : ∀ z, z ∈ [P -[ℝ] Q] → z ∈ [Q -[ℝ] R] → z = Q) :
    ¬ ∃ c : ℝ, 0 < c ∧ R - Q = (-c) • (Q - P) := by
  rintro ⟨c, hc, heq⟩
  let t : ℝ := (1 + c)⁻¹
  have hc0 : 1 + c ≠ 0 := ne_of_gt (by linarith)
  have ht0 : 0 < t := inv_pos.mpr (by linarith)
  have ht1 : t < 1 := by
    dsimp only [t]
    rw [inv_lt_one₀ (by linarith)]
    linarith
  have hf := congrArg Prod.fst heq
  have hs := congrArg Prod.snd heq
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hf hs
  have hline : AffineMap.lineMap P Q t = AffineMap.lineMap Q R t := by
    ext
    · simp only [AffineMap.lineMap_apply_module', Prod.fst_add, Prod.fst_sub,
        Prod.smul_fst, smul_eq_mul, t]
      field_simp
      nlinarith [hf]
    · simp only [AffineMap.lineMap_apply_module', Prod.snd_add, Prod.snd_sub,
        Prod.smul_snd, smul_eq_mul, t]
      field_simp
      nlinarith [hs]
  have hmem1 : AffineMap.lineMap P Q t ∈ [P -[ℝ] Q] := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht0.le, ht1.le⟩, rfl⟩
  have hmem2 : AffineMap.lineMap P Q t ∈ [Q -[ℝ] R] := by
    rw [hline, segment_eq_image_lineMap]
    exact ⟨t, ⟨ht0.le, ht1.le⟩, rfl⟩
  have hz := hinter _ hmem1 hmem2
  have hteq := (AffineMap.lineMap_eq_right_iff.mp hz).resolve_left hPQ
  exact (ne_of_lt ht1) hteq

/-- Every ordinary nondegenerate polygonal corner admits the transverse vector
required by its two actual adjacent quadrilateral strips. -/
theorem exists_transverse_at_corner (P Q R : Plane) (hPQ : P ≠ Q) (hQR : Q ≠ R)
    (hinter : ∀ z, z ∈ [P -[ℝ] Q] → z ∈ [Q -[ℝ] R] → z = Q) :
    ∃ N : Plane, 0 < cross (Q - P) N ∧ 0 < cross (R - Q) N := by
  exact exists_common_transverse (Q - P) (R - Q)
    (sub_ne_zero.mpr hPQ.symm) (sub_ne_zero.mpr hQR.symm)
    (not_opposite_of_segment_intersection P Q R hPQ hinter)

/-- A uniform quantitative tube estimate for the actual scaled strip. -/
theorem dist_stripMap_segment_le (P Q A B : Plane) (ε : ℝ) (p : I × I) :
    dist (stripMap P Q (ε • A) (ε • B) p) ((Path.segment P Q) p.1) ≤
      |ε| * (‖A‖ + ‖B - A‖) := by
  have heq : stripMap P Q (ε • A) (ε • B) p - (Path.segment P Q) p.1 =
      ε • ((p.2 : ℝ) • (A + (p.1 : ℝ) • (B - A))) := by
    simp only [stripMap, ContinuousMap.coe_mk, strip, Path.segment_apply,
      AffineMap.lineMap_apply_module']
    module
  have ht : ‖(p.1 : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
    exact p.1.2.2
  have hs : ‖(p.2 : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg p.2.2.1]
    exact p.2.2.2
  have hinner : ‖A + (p.1 : ℝ) • (B - A)‖ ≤ ‖A‖ + ‖B - A‖ := by
    apply (norm_add_le _ _).trans
    apply add_le_add_left
    exact (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) ht)
  have houter : ‖(p.2 : ℝ) • (A + (p.1 : ℝ) • (B - A))‖ ≤ ‖A‖ + ‖B - A‖ := by
    apply (norm_smul_le _ _).trans
    calc
      _ ≤ 1 * ‖A + (p.1 : ℝ) • (B - A)‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hinner
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left houter (abs_nonneg ε)

end PlanarHom.Polygonal
