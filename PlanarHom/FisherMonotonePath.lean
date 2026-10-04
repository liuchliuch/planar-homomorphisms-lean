import PlanarHom.FisherProjectedOrder

/-! Explicit noncrossing polygonal paths through projection-ordered points. -/
noncomputable section
open Classical Set unitInterval
open scoped Convex

namespace PlanarHom.Fisher
open MultiGraph

def pathSource {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i.val, by omega⟩
def pathTarget {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i.val + 1, by omega⟩

theorem pathSource_lt_target {n : ℕ} (i : Fin (n - 1)) : pathSource i < pathTarget i := by
  change i.val < i.val + 1
  omega

def pointPath (n : ℕ) : MultiGraph (Fin n) (Fin (n - 1)) := ⟨pathSource, pathTarget⟩

def straightCurve (p q : Plane) : C(I, Plane) where
  toFun t := (1 - (t : ℝ)) • p + (t : ℝ) • q
  continuous_toFun := by fun_prop

@[simp] theorem straightCurve_zero (p q : Plane) : straightCurve p q 0 = p := by
  simp [straightCurve]

@[simp] theorem straightCurve_one (p q : Plane) : straightCurve p q 1 = q := by
  simp [straightCurve]

theorem projection_straightCurve (a : ℝ) (p q : Plane) (t : I) :
    linearProjection a (straightCurve p q t) =
      (1 - (t : ℝ)) * linearProjection a p + (t : ℝ) * linearProjection a q := by
  simp only [linearProjection, straightCurve, ContinuousMap.coe_mk, Prod.fst_add,
    Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem straightCurve_projection_inside (a : ℝ) (p q : Plane)
    (hpq : linearProjection a p < linearProjection a q) (t : I) (ht : Inside t) :
    linearProjection a p < linearProjection a (straightCurve p q t) ∧
      linearProjection a (straightCurve p q t) < linearProjection a q := by
  rw [projection_straightCurve]
  constructor <;> nlinarith [ht.1, ht.2]

theorem straightCurve_injective (a : ℝ) (p q : Plane)
    (hpq : linearProjection a p < linearProjection a q) : Function.Injective (straightCurve p q) := by
  intro s t h
  have hh := congrArg (linearProjection a) h
  simp only [projection_straightCurve] at hh
  apply Subtype.ext
  nlinarith

theorem path_projection_avoids {n : ℕ} (p : Fin n → Plane) (a : ℝ)
    (hp : StrictMono (fun i => linearProjection a (p i)))
    (i : Fin (n - 1)) (t : I) (ht : Inside t) (j : Fin n) :
    straightCurve (p (pathSource i)) (p (pathTarget i)) t ≠ p j := by
  intro h
  have hi := straightCurve_projection_inside a _ _ (hp (pathSource_lt_target i)) t ht
  rw [h] at hi
  have hl := hp.lt_iff_lt.mp hi.1
  have hr := hp.lt_iff_lt.mp hi.2
  change i.val < j.val at hl
  change j.val < i.val + 1 at hr
  omega

theorem path_curves_interior_injective {n : ℕ} (p : Fin n → Plane) (a : ℝ)
    (hp : StrictMono (fun i => linearProjection a (p i)))
    (i j : Fin (n - 1)) (s t : I) (hs : Inside s) (ht : Inside t)
    (h : straightCurve (p (pathSource i)) (p (pathTarget i)) s =
      straightCurve (p (pathSource j)) (p (pathTarget j)) t) : i = j ∧ s = t := by
  have his := straightCurve_projection_inside a _ _ (hp (pathSource_lt_target i)) s hs
  have hjt := straightCurve_projection_inside a _ _ (hp (pathSource_lt_target j)) t ht
  have hproj := congrArg (linearProjection a) h
  have he : i = j := by
    apply le_antisymm
    · by_contra hle
      have hji : pathTarget j ≤ pathSource i := by
        change j.val + 1 ≤ i.val
        have := lt_of_not_ge hle
        exact this
      have hh := hp.monotone hji
      linarith
    · by_contra hle
      have hij : pathTarget i ≤ pathSource j := by
        change i.val + 1 ≤ j.val
        have := lt_of_not_ge hle
        exact this
      have hh := hp.monotone hij
      linarith
  subst j
  exact ⟨rfl, straightCurve_injective a _ _ (hp (pathSource_lt_target i)) h⟩

/-- The ordered polyline is an actual ordinary plane drawing. -/
def monotonePathDrawing {n : ℕ} (p : Fin n → Plane) (a : ℝ)
    (hp : StrictMono (fun i => linearProjection a (p i))) : PlaneDrawing (pointPath n) where
  point := p
  point_injective := fun _ _ h => hp.injective (congrArg (linearProjection a) h)
  curve i := straightCurve (p (pathSource i)) (p (pathTarget i))
  curve_zero _ := straightCurve_zero _ _
  curve_one _ := straightCurve_one _ _
  interior_injective := path_curves_interior_injective p a hp
  interior_avoids := path_projection_avoids p a hp

theorem straightCurve_mem_segment (p q : Plane) (t : I) :
    straightCurve p q t ∈ [p -[ℝ] q] := by
  rw [segment_eq_image_lineMap]
  exact ⟨(t : ℝ), t.2, by simp [straightCurve, AffineMap.lineMap_apply_module]⟩

end PlanarHom.Fisher
