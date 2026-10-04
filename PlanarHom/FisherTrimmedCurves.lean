import PlanarHom.FisherProjectedOrder

/-! Actual trimmed edge curves for the vertex-path expansion. -/
noncomputable section
open Set unitInterval

namespace PlanarHom.MultiGraph.PlaneDrawing.Trimming
variable {V E : Type*} {G : MultiGraph V E} {d : PlaneDrawing G} {r : ℝ}
variable (T : d.Trimming r)

def trimParameter (e : E) : C(I, I) where
  toFun t := ⟨(1 - (t : ℝ)) * (T.left e : ℝ) + (t : ℝ) * (T.right e : ℝ), by
    have h := (convex_Icc (0 : ℝ) 1) (T.left e).2 (T.right e).2
      (sub_nonneg.mpr t.2.2) t.2.1 (show (1 - (t : ℝ)) + (t : ℝ) = 1 by ring)
    simpa only [smul_eq_mul] using h⟩
  continuous_toFun := by fun_prop

@[simp] theorem trimParameter_zero (e : E) : T.trimParameter e 0 = T.left e := by
  apply Subtype.ext
  simp [trimParameter]

@[simp] theorem trimParameter_one (e : E) : T.trimParameter e 1 = T.right e := by
  apply Subtype.ext
  simp [trimParameter]

theorem trimParameter_mem (e : E) (t : I) :
    T.trimParameter e t ∈ Set.Icc (T.left e) (T.right e) := by
  have hlt : (T.left e : ℝ) < (T.right e : ℝ) := T.left_lt_right e
  change (T.left e : ℝ) ≤ _ ∧ _ ≤ (T.right e : ℝ)
  dsimp [trimParameter]
  constructor <;> nlinarith [mul_nonneg t.2.1 (sub_nonneg.mpr hlt.le),
    mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr hlt.le)]

theorem trimParameter_mem_open (e : E) (t : I) (ht : Inside t) :
    T.trimParameter e t ∈ Set.Ioo (T.left e) (T.right e) := by
  have hlt : (T.left e : ℝ) < (T.right e : ℝ) := T.left_lt_right e
  change (T.left e : ℝ) < _ ∧ _ < (T.right e : ℝ)
  dsimp [trimParameter]
  constructor <;> nlinarith [mul_pos ht.1 (sub_pos.mpr hlt),
    mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hlt)]

theorem trimParameter_injective (e : E) : Function.Injective (T.trimParameter e) := by
  intro s t h
  have hh := congrArg Subtype.val h
  have hlt : (T.left e : ℝ) < (T.right e : ℝ) := T.left_lt_right e
  apply Subtype.ext
  dsimp [trimParameter] at hh
  nlinarith

def trimmedCurve (e : E) : C(I, Plane) := (d.curve e).comp (T.trimParameter e)

@[simp] theorem trimmedCurve_zero (e : E) : T.trimmedCurve e 0 = T.port (e, false) := by
  simp [trimmedCurve, port]

@[simp] theorem trimmedCurve_one (e : E) : T.trimmedCurve e 1 = T.port (e, true) := by
  simp [trimmedCurve, port]

theorem trimmedCurve_interior_injective (e f : E) (s t : I)
    (h : T.trimmedCurve e s = T.trimmedCurve f t) : e = f ∧ s = t := by
  obtain ⟨hef, hst⟩ := d.interior_injective e f _ _
    (T.middle_inside e (T.trimParameter_mem e s))
    (T.middle_inside f (T.trimParameter_mem f t)) h
  subst f
  exact ⟨rfl, T.trimParameter_injective e hst⟩

theorem trimmedCurve_outside (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    (e : E) (t : I) (ht : Inside t) (v : V) :
    r < dist (T.trimmedCurve e t) (d.point v) :=
  T.middle_strictly_outside hr0 hr e _ (T.trimParameter_mem_open e t ht) v

theorem port_ne_point (p : E × Bool) (v : V) : T.port p ≠ d.point v := by
  rcases p with ⟨e, b⟩
  cases b
  · exact d.interior_avoids e _ (T.left_inside e) v
  · exact d.interior_avoids e _ (T.right_inside e) v

end PlanarHom.MultiGraph.PlaneDrawing.Trimming
