import PlanarHom.FisherMonotonePath
import Mathlib.Tactic.LinearCombination

/-! Elementary coordinates for a triangle inside a convex vertex neighborhood. -/
noncomputable section
open Classical Set unitInterval
open scoped Convex

namespace PlanarHom.Fisher
open MultiGraph

def signedSide (p q z : Plane) : ℝ :=
  (q.1 - p.1) * (z.2 - p.2) - (q.2 - p.2) * (z.1 - p.1)

@[simp] theorem signedSide_left (p q : Plane) : signedSide p q p = 0 := by
  simp [signedSide]

@[simp] theorem signedSide_right (p q : Plane) : signedSide p q q = 0 := by
  unfold signedSide
  ring

theorem signedSide_swap (p q z : Plane) : signedSide q p z = -signedSide p q z := by
  unfold signedSide
  ring

theorem signedSide_lineMap (p q x y : Plane) (t : ℝ) :
    signedSide p q (AffineMap.lineMap x y t) =
      (1-t) * signedSide p q x + t * signedSide p q y := by
  simp only [signedSide, AffineMap.lineMap_apply_module, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem projection_lineMap (a : ℝ) (p q : Plane) (t : ℝ) :
    linearProjection a (AffineMap.lineMap p q t) =
      (1-t) * linearProjection a p + t * linearProjection a q := by
  simp only [linearProjection, AffineMap.lineMap_apply_module, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem signedSide_straightCurve (p q x y : Plane) (t : I) :
    signedSide p q (straightCurve x y t) =
      (1-(t:ℝ)) * signedSide p q x + (t:ℝ) * signedSide p q y := by
  simpa [straightCurve, AffineMap.lineMap_apply_module] using signedSide_lineMap p q x y (t : ℝ)

theorem projection_side_injective (a : ℝ) (p q : Plane)
    (hpq : linearProjection a q ≠ linearProjection a p) :
    Function.Injective (fun z => (linearProjection a z, signedSide p q z)) := by
  intro z w h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hm : (linearProjection a q - linearProjection a p) * (z.2 - w.2) = 0 := by
    dsimp [linearProjection, signedSide] at hx hy ⊢
    linear_combination hy + (q.2 - p.2) * hx
  have hzw : z.2 = w.2 := sub_eq_zero.mp
    ((mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hpq))
  apply Prod.ext
  · dsimp [linearProjection] at hx
    rw [hzw] at hx
    linarith
  · exact hzw

theorem eq_lineMap_of_side_zero (a : ℝ) (p q z : Plane)
    (hpq : linearProjection a q ≠ linearProjection a p) (hz : signedSide p q z = 0) :
    z = AffineMap.lineMap p q
      ((linearProjection a z - linearProjection a p) /
        (linearProjection a q - linearProjection a p)) := by
  apply projection_side_injective a p q hpq
  apply Prod.ext
  · dsimp only
    rw [projection_lineMap]
    have hd := sub_ne_zero.mpr hpq
    field_simp
    ring
  · simp [signedSide_lineMap, hz]

/-- Three different sphere points cannot be collinear with the center. The
middle point is ordered by a strict projection, including flat norm spheres. -/
theorem sphere_middle_center_side_ne (a : ℝ) (p b q c : Plane) (r : ℝ)
    (hr : 0 < r) (hp : dist p c = r) (hb : dist b c = r) (hq : dist q c = r)
    (hpb : linearProjection a p < linearProjection a b)
    (hbq : linearProjection a b < linearProjection a q)
    (hside : signedSide p q b = 0) : signedSide p q c ≠ 0 := by
  intro hc
  have hpq : linearProjection a p < linearProjection a q := hpb.trans hbq
  have hpqne : p ≠ q := by intro h; simp [h] at hpq
  have hdist : 0 < dist p q := dist_pos.mpr hpqne
  let t := (linearProjection a b - linearProjection a p) /
    (linearProjection a q - linearProjection a p)
  let u := (linearProjection a c - linearProjection a p) /
    (linearProjection a q - linearProjection a p)
  have ht0 : 0 < t := div_pos (sub_pos.mpr hpb) (sub_pos.mpr hpq)
  have ht1 : t < 1 := (div_lt_one (sub_pos.mpr hpq)).mpr (by linarith)
  have hbline : b = AffineMap.lineMap p q t := eq_lineMap_of_side_zero a p q b hpq.ne' hside
  have hcline : c = AffineMap.lineMap p q u := eq_lineMap_of_side_zero a p q c hpq.ne' hc
  have hleft : |u| * dist p q = r := by
    have h := hp
    rw [dist_comm, hcline, dist_lineMap_left, Real.norm_eq_abs] at h
    exact h
  have hright : |1-u| * dist p q = r := by
    have h := hq
    rw [dist_comm, hcline, dist_lineMap_right, Real.norm_eq_abs] at h
    exact h
  have habs : |u| = |1-u| := (mul_right_cancel₀ (ne_of_gt hdist)) (hleft.trans hright.symm)
  have hu : u = 1/2 := by
    rcases abs_eq_abs.mp habs with h | h <;> linarith
  have hmiddle : |t - (1/2 : ℝ)| * dist p q = r := by
    rw [hbline, hcline, dist_lineMap_lineMap, Real.dist_eq, hu] at hb
    exact hb
  have habst : |t - (1/2 : ℝ)| < 1/2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  rw [hu] at hleft
  norm_num at hleft
  nlinarith

def bezierCurve (p c q : Plane) : C(I, Plane) where
  toFun t := (1-(t:ℝ))^2 • p + (2*(t:ℝ)*(1-(t:ℝ))) • c + (t:ℝ)^2 • q
  continuous_toFun := by fun_prop

@[simp] theorem bezierCurve_zero (p c q : Plane) : bezierCurve p c q 0 = p := by
  simp [bezierCurve]

@[simp] theorem bezierCurve_one (p c q : Plane) : bezierCurve p c q 1 = q := by
  simp [bezierCurve]

theorem projection_bezierCurve (a : ℝ) (p c q : Plane) (t : I) :
    linearProjection a (bezierCurve p c q t) =
      (1-(t:ℝ))^2 * linearProjection a p +
        (2*(t:ℝ)*(1-(t:ℝ))) * linearProjection a c + (t:ℝ)^2 * linearProjection a q := by
  simp only [linearProjection, bezierCurve, ContinuousMap.coe_mk, Prod.fst_add,
    Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem signedSide_bezierCurve (p c q : Plane) (t : I) :
    signedSide p q (bezierCurve p c q t) = (2*(t:ℝ)*(1-(t:ℝ))) * signedSide p q c := by
  simp only [signedSide, bezierCurve, ContinuousMap.coe_mk, Prod.fst_add,
    Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem bezierCurve_injective (a : ℝ) (p c q : Plane)
    (hpq : linearProjection a q ≠ linearProjection a p) (hc : signedSide p q c ≠ 0) :
    Function.Injective (bezierCurve p c q) := by
  intro s t h
  have hside := congrArg (signedSide p q) h
  simp only [signedSide_bezierCurve] at hside
  have hcontrol := mul_right_cancel₀ hc hside
  have hproj := congrArg (linearProjection a) h
  simp only [projection_bezierCurve] at hproj
  have he : ((s:ℝ)^2 - (t:ℝ)^2) *
      (linearProjection a q - linearProjection a p) = 0 := by
    linear_combination hproj - (linearProjection a c - linearProjection a p) * hcontrol
  have hsquare : (s:ℝ)^2 = (t:ℝ)^2 := sub_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hpq))
  apply Subtype.ext
  nlinarith [s.2.1, t.2.1]

theorem bezierCurve_side_ne (p c q : Plane) (hc : signedSide p q c ≠ 0)
    (t : I) (ht : Inside t) : signedSide p q (bezierCurve p c q t) ≠ 0 := by
  rw [signedSide_bezierCurve]
  exact mul_ne_zero (ne_of_gt (mul_pos (mul_pos (by norm_num) ht.1) (sub_pos.mpr ht.2))) hc

/-- The curved closing edge remains in any convex set containing its controls. -/
theorem bezierCurve_mem_convex (S : Set Plane) (hS : Convex ℝ S)
    {p c q : Plane} (hp : p ∈ S) (hc : c ∈ S) (hq : q ∈ S) (t : I) :
    bezierCurve p c q t ∈ S := by
  have hpc : straightCurve p c t ∈ S :=
    hS.segment_subset hp hc (straightCurve_mem_segment p c t)
  have hcq : straightCurve c q t ∈ S :=
    hS.segment_subset hc hq (straightCurve_mem_segment c q t)
  have hh : straightCurve (straightCurve p c t) (straightCurve c q t) t ∈ S :=
    hS.segment_subset hpc hcq (straightCurve_mem_segment _ _ t)
  have he : bezierCurve p c q t = straightCurve (straightCurve p c t) (straightCurve c q t) t := by
    apply Prod.ext <;>
      simp only [bezierCurve, straightCurve, ContinuousMap.coe_mk, Prod.fst_add,
        Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  exact he.symm ▸ hh

end PlanarHom.Fisher
