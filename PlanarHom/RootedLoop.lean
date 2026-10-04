import PlanarHom.RootedPlanarity

/-! A literal one-root loop with an explicit polynomial plane curve. -/
noncomputable section
open unitInterval
namespace PlanarHom.RootedGraph
open MultiGraph

def singleLoop : RootedGraph (Fin 0) (Fin 1) where
  src _ := .inl PUnit.unit
  dst _ := .inl PUnit.unit

private def loopCurve : C(I,Plane) where
  toFun t := ((t:ℝ)*(1-(t:ℝ)),(2*(t:ℝ)-1)*(t:ℝ)*(1-(t:ℝ)))
  continuous_toFun := by fun_prop

/-- The curve closes at the root and is injective everywhere else. -/
def singleLoopDrawing : PlaneDrawing singleLoop where
  point _ := (0,0)
  point_injective := by
    rintro (a|a) (b|b) _
    · exact congrArg Sum.inl (Subsingleton.elim a b)
    · exact b.elim0
    · exact a.elim0
    · exact a.elim0
  curve _ := loopCurve
  curve_zero _ := by norm_num [loopCurve]
  curve_one _ := by norm_num [loopCurve]
  interior_injective e f s t hs ht h := by
    refine ⟨Subsingleton.elim e f,?_⟩
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    change (s:ℝ)*(1-(s:ℝ))=(t:ℝ)*(1-(t:ℝ)) at hx
    change (2*(s:ℝ)-1)*(s:ℝ)*(1-(s:ℝ))=(2*(t:ℝ)-1)*(t:ℝ)*(1-(t:ℝ)) at hy
    have hp : 0<(s:ℝ)*(1-(s:ℝ)) := mul_pos hs.1 (sub_pos.mpr hs.2)
    have he : (2*(s:ℝ)-1)*((s:ℝ)*(1-(s:ℝ))) =
        (2*(t:ℝ)-1)*((s:ℝ)*(1-(s:ℝ))) := by
      calc
        _ = (2*(s:ℝ)-1)*(s:ℝ)*(1-(s:ℝ)) := by ring
        _ = (2*(t:ℝ)-1)*(t:ℝ)*(1-(t:ℝ)) := hy
        _ = _ := by rw [hx]; ring
    have hc := mul_right_cancel₀ (ne_of_gt hp) he
    apply Subtype.ext
    linarith
  interior_avoids e t ht v h := by
    have hx := congrArg Prod.fst h
    change (t:ℝ)*(1-(t:ℝ))=0 at hx
    exact (ne_of_gt (mul_pos ht.1 (sub_pos.mpr ht.2))) hx

theorem singleLoop_planar : singleLoop.Planar := ⟨singleLoopDrawing⟩

end PlanarHom.RootedGraph
