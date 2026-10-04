import PlanarHom.FisherTriangleGeometry
import PlanarHom.FisherTriangle

/-! A genuine triangle drawing at three ordered ports of a vertex ball.
Collinear ports on a flat face of the product-norm sphere use a curved closing
edge through the ball; noncollinear ports use their straight closing chord. -/
noncomputable section
open Classical Set unitInterval
open scoped Convex

namespace PlanarHom.Fisher
open MultiGraph

def triangleClosing (p : Fin 3 → Plane) (c : Plane) : C(I, Plane) :=
  if signedSide (p 0) (p 2) (p 1) = 0 then bezierCurve (p 2) c (p 0)
    else straightCurve (p 2) (p 0)

@[simp] theorem triangleClosing_zero (p : Fin 3 → Plane) (c : Plane) :
    triangleClosing p c 0 = p 2 := by simp [triangleClosing]; split_ifs <;> simp

@[simp] theorem triangleClosing_one (p : Fin 3 → Plane) (c : Plane) :
    triangleClosing p c 1 = p 0 := by simp [triangleClosing]; split_ifs <;> simp

variable (p : Fin 3 → Plane) (c : Plane) (r a : ℝ)
variable (hr : 0 < r) (hsphere : ∀ i, dist (p i) c = r)
variable (hp : StrictMono (fun i => linearProjection a (p i)))

include hp

private theorem proj01 : linearProjection a (p 0) < linearProjection a (p 1) := hp (by decide)
private theorem proj12 : linearProjection a (p 1) < linearProjection a (p 2) := hp (by decide)
private theorem proj02 : linearProjection a (p 0) < linearProjection a (p 2) := hp (by decide)

include hr hsphere hp

theorem closing_center_side_ne (h : signedSide (p 0) (p 2) (p 1) = 0) :
    signedSide (p 2) (p 0) c ≠ 0 := by
  rw [signedSide_swap]
  exact neg_ne_zero.mpr (sphere_middle_center_side_ne a (p 0) (p 1) (p 2) c r hr
    (hsphere 0) (hsphere 1) (hsphere 2) (proj01 p a hp) (proj12 p a hp) h)

theorem triangleClosing_injective : Function.Injective (triangleClosing p c) := by
  by_cases h : signedSide (p 0) (p 2) (p 1) = 0
  · rw [triangleClosing, if_pos h]
    exact bezierCurve_injective a _ _ _ (proj02 p a hp).ne
      (closing_center_side_ne p c r a hr hsphere hp h)
  · rw [triangleClosing, if_neg h]
    intro s t he
    have he' := congrArg (linearProjection a) he
    simp only [projection_straightCurve] at he'
    have hx := proj02 p a hp
    apply Subtype.ext
    nlinarith

theorem triangleClosing_ne_path (i : Fin 2) (s t : I) (hs : Inside s) (ht : Inside t) :
    triangleClosing p c s ≠ straightCurve (p (pathSource i)) (p (pathTarget i)) t := by
  intro he
  have hval := congrArg (signedSide (p 0) (p 2)) he
  by_cases h : signedSide (p 0) (p 2) (p 1) = 0
  · have hc := closing_center_side_ne p c r a hr hsphere hp h
    have hn : signedSide (p 0) (p 2) (triangleClosing p c s) ≠ 0 := by
      rw [triangleClosing, if_pos h, signedSide_swap]
      exact neg_ne_zero.mpr (bezierCurve_side_ne _ _ _ hc s hs)
    apply hn
    rw [hval]
    fin_cases i <;> simp [pathSource, pathTarget, signedSide_straightCurve, h]
  · have hz : signedSide (p 0) (p 2) (triangleClosing p c s) = 0 := by
      simp [triangleClosing, h, signedSide_straightCurve]
    have hn : signedSide (p 0) (p 2)
        (straightCurve (p (pathSource i)) (p (pathTarget i)) t) ≠ 0 := by
      fin_cases i
      · simpa [pathSource, pathTarget, signedSide_straightCurve] using
          mul_ne_zero (ne_of_gt ht.1) h
      · simpa [pathSource, pathTarget, signedSide_straightCurve] using
          mul_ne_zero (ne_of_gt (sub_pos.mpr ht.2)) h
    exact hn (hval.symm.trans hz)

theorem triangleClosing_ne_middle (t : I) (ht : Inside t) : triangleClosing p c t ≠ p 1 := by
  intro he
  have hh := congrArg (signedSide (p 0) (p 2)) he
  by_cases h : signedSide (p 0) (p 2) (p 1) = 0
  · have hc := closing_center_side_ne p c r a hr hsphere hp h
    have hn := bezierCurve_side_ne _ _ _ hc t ht
    apply hn
    rw [triangleClosing, if_pos h, signedSide_swap] at hh
    rw [h] at hh
    exact neg_eq_zero.mp hh
  · apply h
    rw [← hh]
    simp [triangleClosing, h, signedSide_straightCurve]

def orderedTriangleCurve (e : Fin 3) : C(I, Plane) :=
  if e = 0 then straightCurve (p 1) (p 2)
  else if e = 1 then triangleClosing p c else straightCurve (p 0) (p 1)

theorem orderedTriangle_interior_injective (e f : Fin 3) (s t : I)
    (hs : Inside s) (ht : Inside t)
    (h : orderedTriangleCurve p c e s = orderedTriangleCurve p c f t) : e = f ∧ s = t := by
  fin_cases e <;> fin_cases f
  · exact ⟨rfl, straightCurve_injective a _ _ (proj12 p a hp) h⟩
  · exact (triangleClosing_ne_path p c r a hr hsphere hp 1 t s ht hs h.symm).elim
  · have h₁ := straightCurve_projection_inside a _ _ (proj12 p a hp) s hs
    have h₂ := straightCurve_projection_inside a _ _ (proj01 p a hp) t ht
    have hh := congrArg (linearProjection a) h
    change linearProjection a (straightCurve (p 1) (p 2) s) =
      linearProjection a (straightCurve (p 0) (p 1) t) at hh
    exfalso
    linarith
  · exact (triangleClosing_ne_path p c r a hr hsphere hp 1 s t hs ht h).elim
  · exact ⟨rfl, triangleClosing_injective p c r a hr hsphere hp h⟩
  · exact (triangleClosing_ne_path p c r a hr hsphere hp 0 s t hs ht h).elim
  · have h₁ := straightCurve_projection_inside a _ _ (proj01 p a hp) s hs
    have h₂ := straightCurve_projection_inside a _ _ (proj12 p a hp) t ht
    have hh := congrArg (linearProjection a) h
    change linearProjection a (straightCurve (p 0) (p 1) s) =
      linearProjection a (straightCurve (p 1) (p 2) t) at hh
    exfalso
    linarith
  · exact (triangleClosing_ne_path p c r a hr hsphere hp 0 t s ht hs h.symm).elim
  · exact ⟨rfl, straightCurve_injective a _ _ (proj01 p a hp) h⟩

theorem orderedTriangle_interior_avoids (e : Fin 3) (t : I) (ht : Inside t) (j : Fin 3) :
    orderedTriangleCurve p c e t ≠ p j := by
  fin_cases e
  · exact path_projection_avoids p a hp 1 t ht j
  · fin_cases j
    · intro h
      have he := triangleClosing_injective p c r a hr hsphere hp
        (h.trans (triangleClosing_one p c).symm)
      have he' := congrArg Subtype.val he
      change (t:ℝ) = 1 at he'
      linarith [ht.2]
    · exact triangleClosing_ne_middle p c r a hr hsphere hp t ht
    · intro h
      have he := triangleClosing_injective p c r a hr hsphere hp
        (h.trans (triangleClosing_zero p c).symm)
      have he' := congrArg Subtype.val he
      change (t:ℝ) = 0 at he'
      linarith [ht.1]
  · exact path_projection_avoids p a hp 0 t ht j

def orderedTriangleDrawing : PlaneDrawing triangle where
  point := p
  point_injective := fun _ _ h => hp.injective (congrArg (linearProjection a) h)
  curve := orderedTriangleCurve p c
  curve_zero := by
    intro e
    fin_cases e
    · exact straightCurve_zero _ _
    · exact triangleClosing_zero _ _
    · exact straightCurve_zero _ _
  curve_one := by
    intro e
    fin_cases e
    · exact straightCurve_one _ _
    · exact triangleClosing_one _ _
    · exact straightCurve_one _ _
  interior_injective := orderedTriangle_interior_injective p c r a hr hsphere hp
  interior_avoids := orderedTriangle_interior_avoids p c r a hr hsphere hp

omit hp in
theorem orderedTriangle_curve_mem_ball (e : Fin 3) (t : I) :
    orderedTriangleCurve p c e t ∈ Metric.closedBall c r := by
  have hball (i : Fin 3) : p i ∈ Metric.closedBall c r := (hsphere i).le
  fin_cases e
  · exact (convex_closedBall _ _).segment_subset (hball 1) (hball 2)
      (straightCurve_mem_segment _ _ t)
  · change triangleClosing p c t ∈ _
    unfold triangleClosing
    split_ifs
    · exact bezierCurve_mem_convex _ (convex_closedBall _ _) (hball 2)
        (Metric.mem_closedBall_self hr.le) (hball 0) t
    · exact (convex_closedBall _ _).segment_subset (hball 2) (hball 0)
        (straightCurve_mem_segment _ _ t)
  · exact (convex_closedBall _ _).segment_subset (hball 0) (hball 1)
      (straightCurve_mem_segment _ _ t)

end PlanarHom.Fisher
