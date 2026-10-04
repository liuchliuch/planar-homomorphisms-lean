import PlanarHom.FiniteCircleFanGap

/-! NEW explicit orientation-preserving circle chart at an actual omitted pole. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.CirclePoleChart
open MultiGraph RadialPottsAssemblyGeometry PlanarityCircleCrossing

def rotate (p q : Plane) : Plane := (p.2*q.1-p.1*q.2,p.1*q.1+p.2*q.2)

theorem unit_sq {p : Plane} (hp : rayLength p=1) : p.1^2+p.2^2=1 := by
  have h := rayLength_sq p
  rw [hp] at h
  norm_num at h
  exact h.symm

theorem rotate_norm_sq (p q : Plane) :
    (rotate p q).1^2+(rotate p q).2^2=(p.1^2+p.2^2)*(q.1^2+q.2^2) := by
  simp only [rotate]
  ring

/-- The selected chart rotation preserves the actual oriented determinant. -/
theorem rotate_cross {p : Plane} (hp : rayLength p=1) (q r : Plane) :
    Polygonal.cross (rotate p q) (rotate p r)=Polygonal.cross q r := by
  calc
    _=(p.1^2+p.2^2)*Polygonal.cross q r := by simp only [rotate,Polygonal.cross]; ring
    _=Polygonal.cross q r := by rw [unit_sq hp,one_mul]

theorem rotate_pole {p : Plane} (hp : rayLength p=1) : rotate p p=(0,1) := by
  apply Prod.ext
  · simp [rotate,mul_comm]
  · simpa only [rotate,pow_two] using unit_sq hp

theorem rotate_injective {p : Plane} (hp : rayLength p=1) : Function.Injective (rotate p) := by
  let back : Plane → Plane := fun q => (p.2*q.1+p.1*q.2,-p.1*q.1+p.2*q.2)
  have hinv (q : Plane) : back (rotate p q)=q := by
    apply Prod.ext
    · change p.2*(p.2*q.1-p.1*q.2)+p.1*(p.1*q.1+p.2*q.2)=q.1
      calc
        _=(p.1^2+p.2^2)*q.1 := by ring
        _=q.1 := by rw [unit_sq hp,one_mul]
    · change -p.1*(p.2*q.1-p.1*q.2)+p.2*(p.1*q.1+p.2*q.2)=q.2
      calc
        _=(p.1^2+p.2^2)*q.2 := by ring
        _=q.2 := by rw [unit_sq hp,one_mul]
  intro q r h
  exact (hinv q).symm.trans ((congrArg back h).trans (hinv r))

theorem rotate_ne_pole {p q : Plane} (hp : rayLength p=1) (hq : q≠p) : rotate p q≠(0,1) := by
  intro h
  exact hq (rotate_injective hp (h.trans (rotate_pole hp).symm))

def height (p q : Plane) : ℝ := (halfPlaneMap (rotate p q)).2

/-- Every point on the unit circle away from the selected pole has its proved
actual Cayley coordinate. -/
theorem height_realizes {p q : Plane} (hp : rayLength p=1) (hq : rayLength q=1) (hne : q≠p) :
    diskMap (0,height p q)=rotate p q := by
  have hn := rotate_ne_pole hp hne
  have hs : (rotate p q).1^2+(rotate p q).2^2=1 := by
    rw [rotate_norm_sq,unit_sq hp,unit_sq hq,one_mul]
  have hfirst : (halfPlaneMap (rotate p q)).1=0 := by
    change (1-(rotate p q).1^2-(rotate p q).2^2)/inverseDen (rotate p q)=0
    have hz : 1-(rotate p q).1^2-(rotate p q).2^2=0 := by linarith
    rw [hz,zero_div]
  have heq : halfPlaneMap (rotate p q)=(0,height p q) := Prod.ext hfirst rfl
  rw [← heq]
  exact diskMap_halfPlaneMap _ hn

theorem height_injective {p q r : Plane} (hp : rayLength p=1)
    (hq : rayLength q=1) (hr : rayLength r=1) (hqne : q≠p) (hrne : r≠p)
    (h : height p q=height p r) : q=r := by
  apply rotate_injective hp
  rw [← height_realizes hp hq hqne,← height_realizes hp hr hrne,h]

/-- Continuous height along an actual pole-avoiding circle path. -/
def heightPath {p : Plane} (hp : rayLength p=1) (f : C(I,Plane))
    (hne : ∀ t, f t≠p) : C(I,ℝ) where
  toFun t := height p (f t)
  continuous_toFun := by
    have hc : Continuous (fun t => rotate p (f t)) := by unfold rotate; fun_prop
    have hd : Continuous (fun t => inverseDen (rotate p (f t))) := by unfold inverseDen; fun_prop
    exact (continuous_const.mul hc.fst).div hd
      (fun t => (inverseDen_pos (rotate_ne_pole hp (hne t))).ne')

end PlanarHom.CirclePoleChart
