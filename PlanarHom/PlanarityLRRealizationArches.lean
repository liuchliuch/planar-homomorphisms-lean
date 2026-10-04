import PlanarHom.PlanarEmbedding
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! NEW explicit parabolic routing of a noninterleaving port matching.
The ranges, injectivity and separation are all proved by real algebra. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.PlanarityLRRealization
open MultiGraph

/-- Strictly separated or strictly nested ordered endpoint intervals. -/
def Noninterleaving (a b c d : ℝ) : Prop :=
  b < c ∨ d < a ∨ (a < c ∧ d < b) ∨ (c < a ∧ b < d)

/-- A literal parabola through two ports on the vertical line x. -/
def arch (x a b : ℝ) : C(I,Plane) where
  toFun t := let y := a+(b-a)*(t:ℝ); (x+(y-a)*(b-y),y)
  continuous_toFun := by fun_prop

@[simp] theorem arch_zero (x a b : ℝ) : arch x a b 0=(x,a) := by
  simp [arch]
@[simp] theorem arch_one (x a b : ℝ) : arch x a b 1=(x,b) := by
  simp [arch]

theorem arch_injective_of_ne (x a b : ℝ) (hab : a≠b) : Function.Injective (arch x a b) := by
  intro s t h
  apply Subtype.ext
  have hh := congrArg Prod.snd h
  change a+(b-a)*(s:ℝ)=a+(b-a)*(t:ℝ) at hh
  have he : (b-a)*((s:ℝ)-(t:ℝ))=0 := by nlinarith
  have hn : b-a≠0 := sub_ne_zero.mpr hab.symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hn)

theorem arch_right_of_ne (x a b : ℝ) (hab : a≠b) (t : I) (ht : Inside t) :
    x < (arch x a b t).1 := by
  have hs : 0<(b-a)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab.symm)
  have hp := mul_pos (mul_pos hs ht.1) (sub_pos.mpr ht.2)
  change x < x+((a+(b-a)*(t:ℝ))-a)*(b-(a+(b-a)*(t:ℝ)))
  nlinarith

theorem arch_height_bounds (x a b : ℝ) (t : I) :
    min a b ≤ (arch x a b t).2 ∧ (arch x a b t).2 ≤ max a b := by
  change min a b ≤ a+(b-a)*(t:ℝ) ∧ a+(b-a)*(t:ℝ) ≤ max a b
  have ht0 := t.2.1
  have ht1 := t.2.2
  by_cases hab : a≤b
  · rw [min_eq_left hab,max_eq_right hab]
    constructor <;> nlinarith
  · have hba := le_of_not_ge hab
    rw [min_eq_right hba,max_eq_left hba]
    constructor <;> nlinarith

theorem arch_first_eq (x a b : ℝ) (t : I) :
    (arch x a b t).1 = x+((arch x a b t).2-min a b)*(max a b-(arch x a b t).2) := by
  by_cases h : a≤b
  · simp [arch,min_eq_left h,max_eq_right h]
  · rw [min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h)]
    simp only [arch,ContinuousMap.coe_mk]
    ring

private theorem nested_products_lt {a b c d y : ℝ} (hac : a<c) (hdb : d<b)
    (hcy : c≤y) (hyd : y≤d) : (y-c)*(d-y) < (y-a)*(b-y) := by
  have hp := mul_pos (sub_pos.mpr hac) (sub_pos.mpr (lt_of_le_of_lt hyd hdb))
  have hn := mul_nonneg (sub_nonneg.mpr hcy) (sub_nonneg.mpr hdb.le)
  nlinarith

/-- Every pair of noninterleaving distinct-endpoint arcs has disjoint entire
ranges, including endpoints. The parametrization may run in either direction. -/
theorem arch_ranges_disjoint_unordered (x a b c d : ℝ) (_hab : a≠b) (_hcd : c≠d)
    (hord : Noninterleaving (min a b) (max a b) (min c d) (max c d)) :
    Disjoint (Set.range (arch x a b)) (Set.range (arch x c d)) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨s,rfl⟩ ⟨t,he⟩
  have hs := arch_height_bounds x a b s
  have ht := arch_height_bounds x c d t
  have hy := congrArg Prod.snd he
  have hx := congrArg Prod.fst he
  rw [arch_first_eq x c d t,arch_first_eq x a b s,hy] at hx
  rw [hy] at ht
  rcases hord with h | h | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · linarith
  · linarith
  · have hh := nested_products_lt h₁ h₂ ht.1 ht.2
    linarith
  · have hh := nested_products_lt h₁ h₂ hs.1 hs.2
    linarith

end PlanarHom.PlanarityLRRealization
