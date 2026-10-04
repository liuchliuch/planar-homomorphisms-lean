import PlanarHom.RadialPottsAssemblyCircleMap
import PlanarHom.PlanarityLRRealizationArches
/- NEW import adaptation: the recovered circle-arch body below does not use
any declaration from the absent RadialPottsTileBoundary module. That unused
import is omitted; the full remaining recovered proof body is unchanged. -/

/-! Explicit circle-boundary routing for a noninterleaving port matching.
The inverse Cayley map is proved injective on the closed right half-plane and
sends its interior strictly into the unit disk. No disk-homeomorphism or planar
routing conclusion is assumed. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph PlanarityLRRealization

theorem arch_nonneg (a b : ℝ) (t : I) : 0≤(arch 0 a b t).1 := by
  change 0≤0+((a+(b-a)*(t:ℝ))-a)*(b-(a+(b-a)*(t:ℝ)))
  have hs := sq_nonneg (b-a)
  have hm := mul_nonneg (mul_nonneg hs t.2.1) (sub_nonneg.mpr t.2.2)
  nlinarith

def diskArch (a b : ℝ) : C(I,Plane) where
  toFun t := diskMap (arch 0 a b t)
  continuous_toFun := by
    have hc : Continuous (fun t : I => cayleyDen (arch 0 a b t)) := by
      unfold cayleyDen
      fun_prop
    have hn : ∀ t : I,cayleyDen (arch 0 a b t)≠0 :=
      fun t => ne_of_gt (cayleyDen_pos _ (arch_nonneg a b t))
    unfold diskMap
    exact (((continuous_const.mul ((arch 0 a b).continuous.snd)).div hc hn).prodMk
      (((((arch 0 a b).continuous.fst.pow 2).add ((arch 0 a b).continuous.snd.pow 2)).sub continuous_const).div hc hn))

@[simp] theorem diskArch_zero (a b : ℝ) : diskArch a b 0=diskMap (0,a) := by
  change diskMap (arch 0 a b 0)=_
  rw [arch_zero]

@[simp] theorem diskArch_one (a b : ℝ) : diskArch a b 1=diskMap (0,b) := by
  change diskMap (arch 0 a b 1)=_
  rw [arch_one]

theorem diskArch_injective (a b : ℝ) (hab : a≠b) : Function.Injective (diskArch a b) := by
  intro s t he
  apply arch_injective_of_ne 0 a b hab
  exact diskMap_injOn (arch_nonneg a b s) (arch_nonneg a b t) he

theorem diskArch_inside (a b : ℝ) (hab : a≠b) (t : I) (ht : Inside t) :
    (diskArch a b t).1^2+(diskArch a b t).2^2<1 := by
  apply diskMap_interior
  exact arch_right_of_ne 0 a b hab t ht

theorem diskArch_disjoint (a b c d : ℝ) (hab : a≠b) (hcd : c≠d)
    (hord : Noninterleaving (min a b) (max a b) (min c d) (max c d)) :
    Disjoint (Set.range (diskArch a b)) (Set.range (diskArch c d)) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨s,rfl⟩ ⟨t,ht⟩
  have he := diskMap_injOn (arch_nonneg c d t) (arch_nonneg a b s) ht
  exact Set.disjoint_left.mp (arch_ranges_disjoint_unordered 0 a b c d hab hcd hord)
    ⟨s,rfl⟩ ⟨t,he⟩

/-- A literal drawing of every noninterleaving matching on named circle ports. -/
def circleDrawing {V E : Type*} (G : MultiGraph V E) (height : V → ℝ)
    (hinj : Function.Injective height)
    (hends : ∀ e,G.src e≠G.dst e)
    (horder : ∀ e f,e≠f→Noninterleaving
      (min (height (G.src e)) (height (G.dst e))) (max (height (G.src e)) (height (G.dst e)))
      (min (height (G.src f)) (height (G.dst f))) (max (height (G.src f)) (height (G.dst f)))) :
    PlaneDrawing G where
  point v := diskMap (0,height v)
  point_injective := by
    intro u v h
    apply hinj
    exact congrArg Prod.snd (diskMap_injOn (show (0:ℝ)≤0 from le_rfl) (show (0:ℝ)≤0 from le_rfl) h)
  curve e := diskArch (height (G.src e)) (height (G.dst e))
  curve_zero e := diskArch_zero _ _
  curve_one e := diskArch_one _ _
  interior_injective := by
    intro e f s t hs ht h
    by_cases hef : e=f
    · subst f
      exact ⟨rfl,diskArch_injective _ _ (hinj.ne (hends e)) h⟩
    · exact (Set.disjoint_left.mp (diskArch_disjoint _ _ _ _
        (hinj.ne (hends e)) (hinj.ne (hends f)) (horder e f hef)) ⟨s,rfl⟩ ⟨t,h.symm⟩).elim
  interior_avoids := by
    intro e t ht v h
    have hi := diskArch_inside _ _ (hinj.ne (hends e)) t ht
    change (diskArch _ _ t).1^2+(diskArch _ _ t).2^2<1 at hi
    rw [h,diskMap_boundary] at hi
    exact (lt_irrefl (1:ℝ) hi)

end PlanarHom.RadialPottsAssemblyGeometry
