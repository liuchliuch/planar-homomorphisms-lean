import PlanarHom.RadialPottsAssemblyCircleMap
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact circular endpoint coordinates of nonvertical polygonal ray fans.
Determinant order becomes ordinary order in the inverse-Cayley boundary chart. -/
noncomputable section
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph Polygonal

def rayLength (p : Plane) : ℝ := Real.sqrt (p.1^2+p.2^2)

def circleRay (p : Plane) : Plane := (p.1/rayLength p,p.2/rayLength p)

def circleHeight (p : Plane) : ℝ := p.1/(rayLength p-p.2)

theorem rayLength_sq (p : Plane) : (rayLength p)^2=p.1^2+p.2^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem rayLength_pos {p : Plane} (hp : p.1≠0) : 0<rayLength p := by
  apply Real.sqrt_pos.2
  have hx : 0<p.1^2 := sq_pos_of_ne_zero hp
  nlinarith [sq_nonneg p.2]

theorem rayLength_gt_y {p : Plane} (hp : p.1≠0) : p.2<rayLength p := by
  have hr := rayLength_pos hp
  have hs := rayLength_sq p
  have hx : 0<p.1^2 := sq_pos_of_ne_zero hp
  nlinarith

theorem circleHeight_den {p : Plane} (hp : p.1≠0) :
    (circleHeight p)^2+1=2*rayLength p/(rayLength p-p.2) := by
  have hd : rayLength p-p.2≠0 := ne_of_gt (sub_pos.mpr (rayLength_gt_y hp))
  unfold circleHeight
  field_simp
  nlinarith [rayLength_sq p]

/-- No existence of a boundary parametrization is assumed: this is its formula. -/
theorem diskMap_circleHeight {p : Plane} (hp : p.1≠0) :
    diskMap (0,circleHeight p)=circleRay p := by
  have hr : rayLength p≠0 := ne_of_gt (rayLength_pos hp)
  have hd : rayLength p-p.2≠0 := ne_of_gt (sub_pos.mpr (rayLength_gt_y hp))
  have hc : cayleyDen (0,circleHeight p)=2*rayLength p/(rayLength p-p.2) := by
    simpa [cayleyDen,add_comm] using circleHeight_den hp
  apply Prod.ext
  · change 2*circleHeight p/cayleyDen (0,circleHeight p)=p.1/rayLength p
    rw [hc]
    unfold circleHeight
    field_simp
  · change (0^2+(circleHeight p)^2-1)/cayleyDen (0,circleHeight p)=p.2/rayLength p
    have hh : (circleHeight p)^2-1=2*rayLength p/(rayLength p-p.2)-2 := by
      have := circleHeight_den hp
      linarith
    simp only [zero_pow (by norm_num : 2≠0),zero_add]
    rw [hh,hc]
    field_simp
    ring

theorem circleRay_norm_sq {p : Plane} (hp : p.1≠0) :
    (circleRay p).1^2+(circleRay p).2^2=1 := by
  rw [← diskMap_circleHeight hp]
  exact diskMap_boundary _

theorem circleRay_cross (p q : Plane) :
    cross (circleRay p) (circleRay q)=cross p q/(rayLength p*rayLength q) := by
  simp only [circleRay,cross]
  ring

theorem diskMap_boundary_cross (a b : ℝ) :
    cross (diskMap (0,a)) (diskMap (0,b))=
      2*(b-a)*(a*b+1)/((a^2+1)*(b^2+1)) := by
  have ha : a^2+1≠0 := by positivity
  have hb : b^2+1≠0 := by positivity
  simp [diskMap,cayleyDen,cross]
  field_simp
  ring

theorem circleHeight_sign {p : Plane} (hp : p.1≠0) :
    (0<circleHeight p ↔ 0<p.1) ∧ (circleHeight p<0 ↔ p.1<0) := by
  have hd : 0<rayLength p-p.2 := sub_pos.mpr (rayLength_gt_y hp)
  constructor
  · exact div_pos_iff_of_pos_right hd
  · simpa only [zero_mul] using (div_lt_iff₀ hd : p.1/(rayLength p-p.2)<0 ↔ p.1<0*(rayLength p-p.2))

/-- Within either rightward or leftward clusters, strict clockwise determinant
order gives strict decreasing boundary height. -/
theorem circleHeight_clockwise {p q : Plane} (hsign : 0<p.1*q.1)
    (hcross : cross p q<0) : circleHeight q<circleHeight p := by
  have hp : p.1≠0 := by intro h; simp [h] at hsign
  have hq : q.1≠0 := by intro h; simp [h] at hsign
  have hmul : 0<circleHeight p*circleHeight q := by
    unfold circleHeight
    rw [div_mul_div_comm]
    exact div_pos hsign (mul_pos (sub_pos.mpr (rayLength_gt_y hp))
      (sub_pos.mpr (rayLength_gt_y hq)))
  have hc : cross (circleRay p) (circleRay q)<0 := by
    rw [circleRay_cross]
    exact div_neg_of_neg_of_pos hcross (mul_pos (rayLength_pos hp) (rayLength_pos hq))
  rw [← diskMap_circleHeight hp,← diskMap_circleHeight hq,diskMap_boundary_cross] at hc
  have hn := (div_lt_iff₀ (by positivity :
    0<((circleHeight p)^2+1)*((circleHeight q)^2+1))).mp hc
  have hfac : 0<circleHeight p*circleHeight q+1 := by linarith
  have hd : circleHeight q-circleHeight p<0 := by nlinarith
  linarith


theorem continuous_rayLength : Continuous rayLength := by
  unfold rayLength
  fun_prop

theorem rayLength_pos_of_ne_zero {p : Plane} (hp : p≠0) : 0<rayLength p := by
  by_cases hx : p.1=0
  · have hy : p.2≠0 := by
      intro h
      apply hp
      exact Prod.ext hx h
    apply Real.sqrt_pos.2
    have hs := sq_pos_of_ne_zero hy
    simpa [hx] using hs
  · exact rayLength_pos hx

theorem rayLength_nonneg (p : Plane) : 0≤rayLength p := Real.sqrt_nonneg _

theorem rayLength_smul (r : ℝ) (p : Plane) : rayLength (r • p)= |r| * rayLength p := by
  have he : (r*p.1)^2+(r*p.2)^2=r^2*(p.1^2+p.2^2) := by ring
  change Real.sqrt ((r*p.1)^2+(r*p.2)^2)=_
  rw [he,Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq_eq_abs]
  rfl

theorem norm_le_rayLength (p : Plane) : ‖p‖≤rayLength p := by
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  apply max_le
  · have hr := rayLength_nonneg p
    have hs := rayLength_sq p
    have ha := sq_abs p.1
    nlinarith [sq_nonneg p.2,abs_nonneg p.1]
  · have hr := rayLength_nonneg p
    have hs := rayLength_sq p
    have ha := sq_abs p.2
    nlinarith [sq_nonneg p.1,abs_nonneg p.2]

theorem circleRay_rayLength {p : Plane} (hp : p≠0) : rayLength (circleRay p)=1 := by
  have hr := rayLength_pos_of_ne_zero hp
  have he : circleRay p=(1/rayLength p) • p := by
    apply Prod.ext <;> simp [circleRay,div_eq_mul_inv,mul_comm]
  rw [he,rayLength_smul,abs_of_pos (one_div_pos.mpr hr)]
  field_simp

end PlanarHom.RadialPottsAssemblyGeometry
