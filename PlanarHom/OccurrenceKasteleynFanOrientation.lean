import PlanarHom.OccurrenceKasteleynHostFanChart

/-! NEW exact orientation of the actual host fan intervals. This identifies
which transverse endpoint is the minimum/maximum chart height and proves the
source/target reversal needed by the literal tree-contour permutation. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom

private theorem exists_positive_product_near_zero (f : C(I,ℝ)) :
    ∃ t : I, (0:ℝ)<t ∧ 0<f 0*f t+1 := by
  have hc : Continuous (fun t => f 0*f t+1) := (continuous_const.mul f.continuous).add continuous_const
  have ho : IsOpen {t : I | 0<f 0*f t+1} := isOpen_lt continuous_const hc
  have h0 : (0:I)∈{t : I | 0<f 0*f t+1} := by
    change 0<f 0*f 0+1
    nlinarith [sq_nonneg (f 0)]
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho 0 h0
  let t : I := ⟨min (ε/2) (1/2),⟨(lt_min (by linarith) (by norm_num)).le,
    (min_le_right _ _).trans (by norm_num)⟩⟩
  have ht : (0:ℝ)<t := lt_min (by linarith) (by norm_num)
  refine ⟨t,ht,hball ?_⟩
  change dist (t:ℝ) 0<ε
  rw [Real.dist_eq,sub_zero,abs_of_pos ht]
  have hh : (t:ℝ)≤ε/2 := min_le_left _ _
  linarith

namespace MultiGraph.PolygonalDrawing.TwoSidedStripData
open Kasteleyn Polygonal RadialPottsAssemblyGeometry
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable {v : V} (H : HostFanChart F v)

namespace HostFanChart

theorem cross_height (a : HostDart G v) (s t : I) :
    cross (diskMap (0,H.height a s)) (diskMap (0,H.height a t)) =
      cross ((F a.val).direction s) ((F a.val).direction t) /
        (rayLength ((F a.val).direction s)*rayLength ((F a.val).direction t)) := by
  rw [H.realizes,H.realizes,CirclePoleChart.rotate_cross H.pole_circle]
  exact circleRay_cross _ _

/-- The chart's strict orientation is forced by the actual fan determinant.
Only a sufficiently close pair is used for the local Cayley sign; continuity
and injectivity then fix the orientation on the whole closed fan. -/
theorem height_orientation (a : HostDart G v) :
    if positive=a.val.2 then StrictMono (H.height a) else StrictAnti (H.height a) := by
  obtain ⟨t,ht,hfac⟩ := exists_positive_product_near_zero (H.height a)
  have hlen : 0<rayLength ((F a.val).direction 0)*rayLength ((F a.val).direction t) :=
    mul_pos (rayLength_pos_of_ne_zero ((F a.val).direction_ne_zero 0))
      (rayLength_pos_of_ne_zero ((F a.val).direction_ne_zero t))
  have hden : 0<((H.height a 0)^2+1)*((H.height a t)^2+1) := by positivity
  have hraw := (F a.val).direction_order ht
  split_ifs with hside
  · have hcross : 0<cross (diskMap (0,H.height a 0)) (diskMap (0,H.height a t)) := by
      rw [H.cross_height]
      exact div_pos (by simpa only [hside,if_true] using hraw) hlen
    rw [diskMap_boundary_cross] at hcross
    have hnum := (lt_div_iff₀ hden).mp hcross
    have hd : 0<2*(H.height a t-H.height a 0) :=
      (mul_lt_mul_iff_left₀ hfac).mp (by simpa only [zero_mul] using hnum)
    have hearly : H.height a 0<H.height a t := by linarith
    rcases H.height_monotone a with hm | hm
    · exact hm
    · exact False.elim (lt_asymm hearly (hm (show (0:I)<t from ht)))
  · have hcross : cross (diskMap (0,H.height a 0)) (diskMap (0,H.height a t))<0 := by
      rw [H.cross_height]
      exact div_neg_of_neg_of_pos (by simpa only [hside,if_false] using hraw) hlen
    rw [diskMap_boundary_cross] at hcross
    have hnum := (div_lt_iff₀ hden).mp hcross
    have hd : 2*(H.height a t-H.height a 0)<0 :=
      (mul_lt_mul_iff_left₀ hfac).mp (by simpa only [zero_mul] using hnum)
    have hearly : H.height a t<H.height a 0 := by linarith
    rcases H.height_monotone a with hm | hm
    · exact False.elim (lt_asymm hearly (hm (show (0:I)<t from ht)))
    · exact hm

/-- Transverse endpoint at which the positively scanned circle enters a fan. -/
def enterParameter (positive : Bool) (a : Dart E) : I := if positive=a.2 then 0 else 1
/-- Transverse endpoint at which the positively scanned circle leaves a fan. -/
def exitParameter (positive : Bool) (a : Dart E) : I := if positive=a.2 then 1 else 0

theorem lower_eq_enter (a : HostDart G v) : H.lower a=H.height a (enterParameter positive a.val) := by
  have hh := H.height_orientation a
  unfold lower enterParameter
  split_ifs with hs
  · simp only [hs,if_true] at hh
    exact min_eq_left (hh.monotone bot_le)
  · simp only [hs,if_false] at hh
    exact min_eq_right (hh.antitone bot_le)

theorem upper_eq_exit (a : HostDart G v) : H.upper a=H.height a (exitParameter positive a.val) := by
  have hh := H.height_orientation a
  unfold upper exitParameter
  split_ifs with hs
  · simp only [hs,if_true] at hh
    exact max_eq_right (hh.monotone bot_le)
  · simp only [hs,if_false] at hh
    exact max_eq_left (hh.antitone bot_le)

omit [Fintype E] in
@[simp] theorem enter_eq_exit_reverse (positive : Bool) (a : Dart E) :
    enterParameter positive a=exitParameter positive (a.1,!a.2) := by
  rcases a with ⟨e,b⟩
  cases positive <;> cases b <;> rfl

omit [Fintype E] in
@[simp] theorem enter_ne_exit (positive : Bool) (a : Dart E) :
    enterParameter positive a≠exitParameter positive a := by
  unfold enterParameter exitParameter
  split_ifs <;> norm_num

end HostFanChart
end MultiGraph.PolygonalDrawing.TwoSidedStripData
end PlanarHom
