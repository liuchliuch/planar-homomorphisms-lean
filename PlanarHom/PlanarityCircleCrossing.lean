import PlanarHom.PlanarityHalfPlaneCrossing
import PlanarHom.RadialPottsAssemblyCircleCoordinates
import PlanarHom.PlanarNeighborhoods

/-! NEW cyclic port crossing, transported through the actual inverse Cayley map.
The half-plane crossing theorem supplies the topological obstruction. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.PlanarityCircleCrossing
open MultiGraph PlaneDrawing RadialPottsAssemblyGeometry PlanarityHalfPlaneCrossing

/-- The inverse Cayley denominator vanishes at exactly the omitted north pole. -/
theorem inverseDen_pos {q : Plane} (hq : q≠(0,1)) : 0 < inverseDen q := by
  by_cases hx : q.1=0
  · have hy : 1-q.2≠0 := by
      intro h
      exact hq (Prod.ext hx (by linarith))
    unfold inverseDen
    nlinarith [sq_pos_of_ne_zero hy,sq_nonneg q.1]
  · unfold inverseDen
    nlinarith [sq_pos_of_ne_zero hx,sq_nonneg (1-q.2)]

theorem cayleyDen_halfPlaneMap (q : Plane) (hq : inverseDen q≠0) :
    cayleyDen (halfPlaneMap q)=4/inverseDen q := by
  unfold cayleyDen halfPlaneMap
  dsimp
  field_simp
  unfold inverseDen
  ring

theorem diskMap_halfPlaneMap (q : Plane) (hq : q≠(0,1)) :
    diskMap (halfPlaneMap q)=q := by
  have hd := (inverseDen_pos hq).ne'
  unfold diskMap
  rw [cayleyDen_halfPlaneMap q hd]
  apply Prod.ext <;> dsimp [halfPlaneMap]
  · field_simp
    ring
  · field_simp
    unfold inverseDen
    ring

theorem halfPlaneMap_injOn : Set.InjOn halfPlaneMap {q : Plane | q≠(0,1)} := by
  intro p hp q hq h
  calc p = diskMap (halfPlaneMap p) := (diskMap_halfPlaneMap p hp).symm
       _ = diskMap (halfPlaneMap q) := congrArg diskMap h
       _ = q := diskMap_halfPlaneMap q hq

theorem diskMap_boundary_ne_pole (a : ℝ) : diskMap (0,a)≠(0,1) := by
  intro h
  have hd := inverseDen_diskMap (0,a) (cayleyDen_pos (0,a) (by simp)).ne'
  rw [h] at hd
  have hp : 0<4/cayleyDen (0,a) := div_pos (by norm_num) (cayleyDen_pos (0,a) (by simp))
  norm_num [inverseDen] at hd
  linarith

/-- Swap the inverse coordinates and reflect to send the exterior of the unit
circle to the upper half-plane; Cayley boundary parameter a becomes (a,0). -/
def outsideTransform (q : Plane) : Plane := ((halfPlaneMap q).2,-(halfPlaneMap q).1)

@[simp] theorem outsideTransform_boundary (a : ℝ) : outsideTransform (diskMap (0,a))=(a,0) := by
  simp [outsideTransform,halfPlaneMap_diskMap (0,a) (by simp)]

theorem outsideTransform_injective {p q : Plane} (hp : p≠(0,1)) (hq : q≠(0,1))
    (h : outsideTransform p=outsideTransform q) : p=q := by
  apply halfPlaneMap_injOn hp hq
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  exact Prod.ext (neg_injective h₂) h₁

def outsidePath (p : C(I,Plane)) (hp : ∀ t, p t≠(0,1)) : C(I,Plane) where
  toFun t := outsideTransform (p t)
  continuous_toFun := by
    have hd : Continuous (fun t => inverseDen (p t)) := by unfold inverseDen; fun_prop
    have hn : ∀ t, inverseDen (p t)≠0 := fun t => (inverseDen_pos (hp t)).ne'
    exact ((continuous_const.mul p.continuous.fst).div hd hn).prodMk
      ((((continuous_const.sub (p.continuous.fst.pow 2)).sub (p.continuous.snd.pow 2)).div hd hn).neg)

theorem outsideTransform_upper {q : Plane} (hp : q≠(0,1)) (hq : 1≤q.1^2+q.2^2) :
    0≤(outsideTransform q).2 := by
  change 0 ≤ -((1-q.1^2-q.2^2)/inverseDen q)
  exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) (inverseDen_pos hp).le)

/-- Actual continuous exterior-circle arcs with alternating Cayley boundary
ports must intersect. No cyclic ordering certificate is assumed. -/
theorem alternating_circle_paths_intersect (α β : C(I,Plane)) {a b c d : ℝ}
    (hab : a<b) (hbc : b<c) (hcd : c<d)
    (ha : α 0=diskMap (0,a)) (hc : α 1=diskMap (0,c))
    (hb : β 0=diskMap (0,b)) (hd : β 1=diskMap (0,d))
    (hα : ∀ t, 1≤(α t).1^2+(α t).2^2) (hβ : ∀ t, 1≤(β t).1^2+(β t).2^2)
    (hαpole : ∀ t, α t≠(0,1)) (hβpole : ∀ t, β t≠(0,1)) :
    ∃ s t, α s=β t := by
  obtain ⟨s,t,h⟩ := alternating_plane_paths_intersect (outsidePath α hαpole) (outsidePath β hβpole)
    hab hbc hcd
    (by change outsideTransform (α 0)=_; rw [ha,outsideTransform_boundary])
    (by change outsideTransform (α 1)=_; rw [hc,outsideTransform_boundary])
    (by change outsideTransform (β 0)=_; rw [hb,outsideTransform_boundary])
    (by change outsideTransform (β 1)=_; rw [hd,outsideTransform_boundary])
    (fun t => outsideTransform_upper (hαpole t) (hα t))
    (fun t => outsideTransform_upper (hβpole t) (hβ t))
  exact ⟨s,t,outsideTransform_injective (hαpole s) (hβpole t) h⟩

/-- Strictly exterior interiors derive all pole-avoidance and closed-half-plane
hypotheses, including both boundary endpoints. -/
theorem alternating_strict_circle_paths_intersect (α β : C(I,Plane)) {a b c d : ℝ}
    (hab : a<b) (hbc : b<c) (hcd : c<d)
    (ha : α 0=diskMap (0,a)) (hc : α 1=diskMap (0,c))
    (hb : β 0=diskMap (0,b)) (hd : β 1=diskMap (0,d))
    (hα : ∀ t, Inside t → 1<(α t).1^2+(α t).2^2)
    (hβ : ∀ t, Inside t → 1<(β t).1^2+(β t).2^2) :
    ∃ s t, α s=β t := by
  have hpath (p : C(I,Plane)) (u v : ℝ) (h0 : p 0=diskMap (0,u)) (h1 : p 1=diskMap (0,v))
      (hh : ∀ t, Inside t → 1<(p t).1^2+(p t).2^2) :
      (∀ t, 1≤(p t).1^2+(p t).2^2) ∧ ∀ t, p t≠(0,1) := by
    have hcases (t : I) : t=0 ∨ t=1 ∨ Inside t := by
      by_cases ht0 : t=0
      · exact Or.inl ht0
      by_cases ht1 : t=1
      · exact Or.inr (Or.inl ht1)
      · exact Or.inr (Or.inr (inside_of_ne_endpoints ht0 ht1))
    constructor
    · intro t
      rcases hcases t with rfl | rfl | ht
      · rw [h0,diskMap_boundary]
      · rw [h1,diskMap_boundary]
      · exact (hh t ht).le
    · intro t
      rcases hcases t with rfl | rfl | ht
      · rw [h0]; exact diskMap_boundary_ne_pole u
      · rw [h1]; exact diskMap_boundary_ne_pole v
      · intro he
        have hlt := hh t ht
        norm_num [he] at hlt
  have hA := hpath α a c ha hc hα
  have hB := hpath β b d hb hd hβ
  exact alternating_circle_paths_intersect α β hab hbc hcd ha hc hb hd hA.1 hB.1 hA.2 hB.2

/-- Translation and positive scaling connect the circle obstruction to literal
circle-clipped drawing curves at their actual vertex positions and radius. -/
theorem alternating_scaledCircle_paths_intersect (α β : C(I,Plane)) (v : Plane)
    (R : ℝ) (hR : 0<R) {a b c d : ℝ} (hab : a<b) (hbc : b<c) (hcd : c<d)
    (ha : α 0=v+R • diskMap (0,a)) (hc : α 1=v+R • diskMap (0,c))
    (hb : β 0=v+R • diskMap (0,b)) (hd : β 1=v+R • diskMap (0,d))
    (hα : ∀ t, Inside t → R<rayLength (α t-v))
    (hβ : ∀ t, Inside t → R<rayLength (β t-v)) : ∃ s t, α s=β t := by
  let A : C(I,Plane) := ⟨fun t => R⁻¹ • (α t-v),
    continuous_const.smul (α.continuous.sub continuous_const)⟩
  let B : C(I,Plane) := ⟨fun t => R⁻¹ • (β t-v),
    continuous_const.smul (β.continuous.sub continuous_const)⟩
  have hnorm (p : Plane) (hp : R<rayLength (p-v)) :
      1<(R⁻¹ • (p-v)).1^2+(R⁻¹ • (p-v)).2^2 := by
    have hh : 1<rayLength (R⁻¹ • (p-v)) := by
      rw [rayLength_smul,abs_of_pos (inv_pos.mpr hR),← div_eq_inv_mul]
      exact (lt_div_iff₀ hR).mpr (by simpa using hp)
    nlinarith [rayLength_sq (R⁻¹ • (p-v))]
  obtain ⟨s,t,h⟩ := alternating_strict_circle_paths_intersect A B hab hbc hcd
    (by change R⁻¹ • (α 0-v)=_; rw [ha,add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hR.ne',one_smul])
    (by change R⁻¹ • (α 1-v)=_; rw [hc,add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hR.ne',one_smul])
    (by change R⁻¹ • (β 0-v)=_; rw [hb,add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hR.ne',one_smul])
    (by change R⁻¹ • (β 1-v)=_; rw [hd,add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hR.ne',one_smul])
    (fun t ht => hnorm _ (hα t ht)) (fun t ht => hnorm _ (hβ t ht))
  have hh := congrArg (fun q : Plane => R • q) h
  change R • (R⁻¹ • (α s-v))=R • (R⁻¹ • (β t-v)) at hh
  simp only [smul_smul,mul_inv_cancel₀ hR.ne',one_smul] at hh
  exact ⟨s,t,sub_left_inj.mp hh⟩

end PlanarHom.PlanarityCircleCrossing
