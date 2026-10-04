import PlanarHom.PlanarEmbedding
import Mathlib.Tactic.FinCases

/-! Finite integer certificates for literal straight-line plane drawings. The
certificate checks integer inequalities; its soundness constructs and proves
continuous curves with disjoint open interiors and vertex avoidance. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.IntegerStraightDrawing
open MultiGraph

abbrev Point := ℤ × ℤ

def toPlane (p : Point) : Plane := ((p.1:ℝ),(p.2:ℝ))
def orient (a b c : Point) : ℤ := (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)
def realOrient (a b c : Plane) : ℝ := (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)
def affine (a b : Plane) (t : ℝ) : Plane := ((1-t)*a.1+t*b.1,(1-t)*a.2+t*b.2)

def sameSide (a b c d : Point) : Prop :=
  0≤orient a b c ∧ 0≤orient a b d ∧ (0<orient a b c ∨ 0<orient a b d)

def coordinateSeparate (a b c d : ℤ) : Prop :=
  a≠b ∧ c≠d ∧ (max a b≤min c d ∨ max c d≤min a b)

def Separated (a b c d : Point) : Prop :=
  sameSide a b c d ∨ sameSide b a c d ∨ sameSide c d a b ∨ sameSide d c a b ∨
    coordinateSeparate a.1 b.1 c.1 d.1 ∨ coordinateSeparate a.2 b.2 c.2 d.2

def coordinateAvoid (a b c : ℤ) : Prop := a≠b ∧ (c≤min a b ∨ max a b≤c)
def Avoids (a b p : Point) : Prop :=
  orient a b p≠0 ∨ coordinateAvoid a.1 b.1 p.1 ∨ coordinateAvoid a.2 b.2 p.2

instance (a b c d : Point) : Decidable (Separated a b c d) :=
  by unfold Separated sameSide coordinateSeparate; infer_instance
instance (a b p : Point) : Decidable (Avoids a b p) :=
  by unfold Avoids coordinateAvoid; infer_instance

@[simp] theorem realOrient_cast (a b c : Point) :
    realOrient (toPlane a) (toPlane b) (toPlane c)=(orient a b c : ℝ) := by
  simp [realOrient,toPlane,orient]

theorem realOrient_affine (a b c d : Plane) (t : ℝ) :
    realOrient a b (affine c d t)=(1-t)*realOrient a b c+t*realOrient a b d := by
  dsimp [realOrient,affine]
  ring

@[simp] theorem realOrient_segment (a b : Plane) (t : ℝ) :
    realOrient a b (affine a b t)=0 := by dsimp [realOrient,affine]; ring

private theorem sameSide_positive (a b c d : Point) (t : ℝ) (ht0 : 0<t) (ht1 : t<1)
    (h : sameSide a b c d) :
    0<realOrient (toPlane a) (toPlane b) (affine (toPlane c) (toPlane d) t) := by
  rcases h with ⟨hc,hd,hc | hd⟩
  all_goals rw [realOrient_affine,realOrient_cast,realOrient_cast]
  · have hc0 : (0:ℝ)<orient a b c := by exact_mod_cast hc
    have hd0 : (0:ℝ)≤orient a b d := by exact_mod_cast hd
    nlinarith [mul_pos (show 0<1-t by linarith) hc0,mul_nonneg ht0.le hd0]
  · have hc0 : (0:ℝ)≤orient a b c := by exact_mod_cast hc
    have hd0 : (0:ℝ)<orient a b d := by exact_mod_cast hd
    nlinarith [mul_nonneg (show 0≤1-t by linarith) hc0,mul_pos ht0 hd0]

private theorem affine_strict_bounds (a b t : ℝ) (hab : a≠b) (ht0 : 0<t) (ht1 : t<1) :
    min a b<(1-t)*a+t*b ∧ (1-t)*a+t*b<max a b := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [min_eq_left h.le,max_eq_right h.le]
    constructor <;> nlinarith [mul_pos ht0 (sub_pos.mpr h),mul_pos (show 0<1-t by linarith) (sub_pos.mpr h)]
  · rw [min_eq_right h.le,max_eq_left h.le]
    constructor <;> nlinarith [mul_pos ht0 (sub_pos.mpr h),mul_pos (show 0<1-t by linarith) (sub_pos.mpr h)]

private theorem coordinateSeparate_ne (a b c d : ℤ) (s t : ℝ)
    (hs0 : 0<s) (hs1 : s<1) (ht0 : 0<t) (ht1 : t<1) (h : coordinateSeparate a b c d) :
    (1-s)*(a:ℝ)+s*b≠(1-t)*(c:ℝ)+t*d := by
  rcases h with ⟨hab,hcd,hsep⟩
  have hab' : (a:ℝ)≠b := by exact_mod_cast hab
  have hcd' : (c:ℝ)≠d := by exact_mod_cast hcd
  have hs := affine_strict_bounds a b s hab' hs0 hs1
  have ht := affine_strict_bounds c d t hcd' ht0 ht1
  rcases hsep with hsep | hsep
  · have hh : max (a:ℝ) b≤min (c:ℝ) d := by exact_mod_cast hsep
    linarith
  · have hh : max (c:ℝ) d≤min (a:ℝ) b := by exact_mod_cast hsep
    linarith

/-- Sound integer separation certificate; no numerical or trusted tactic. -/
theorem separated_ne (a b c d : Point) (s t : ℝ)
    (hs0 : 0<s) (hs1 : s<1) (ht0 : 0<t) (ht1 : t<1) (h : Separated a b c d) :
    affine (toPlane a) (toPlane b) s≠affine (toPlane c) (toPlane d) t := by
  intro he
  rcases h with h | h | h | h | h | h
  · have hp := sameSide_positive a b c d t ht0 ht1 h
    rw [←he,realOrient_segment] at hp
    linarith
  · have hp := sameSide_positive b a c d t ht0 ht1 h
    rw [←he] at hp
    have hz : realOrient (toPlane b) (toPlane a) (affine (toPlane a) (toPlane b) s)=0 := by
      dsimp [realOrient,affine]
      ring
    rw [hz] at hp
    linarith
  · have hp := sameSide_positive c d a b s hs0 hs1 h
    rw [he,realOrient_segment] at hp
    linarith
  · have hp := sameSide_positive d c a b s hs0 hs1 h
    rw [he] at hp
    have hz : realOrient (toPlane d) (toPlane c) (affine (toPlane c) (toPlane d) t)=0 := by
      dsimp [realOrient,affine]
      ring
    rw [hz] at hp
    linarith
  · exact coordinateSeparate_ne _ _ _ _ _ _ hs0 hs1 ht0 ht1 h (congrArg Prod.fst he)
  · exact coordinateSeparate_ne _ _ _ _ _ _ hs0 hs1 ht0 ht1 h (congrArg Prod.snd he)

private theorem coordinateAvoid_ne (a b c : ℤ) (t : ℝ) (ht0 : 0<t) (ht1 : t<1)
    (h : coordinateAvoid a b c) : (1-t)*(a:ℝ)+t*b≠c := by
  rcases h with ⟨hab,hc⟩
  have hab' : (a:ℝ)≠b := by exact_mod_cast hab
  have ht := affine_strict_bounds a b t hab' ht0 ht1
  rcases hc with hc | hc
  · have hh : (c:ℝ)≤min (a:ℝ) b := by exact_mod_cast hc
    linarith
  · have hh : max (a:ℝ) b≤c := by exact_mod_cast hc
    linarith

theorem avoids_ne (a b p : Point) (t : ℝ) (ht0 : 0<t) (ht1 : t<1) (h : Avoids a b p) :
    affine (toPlane a) (toPlane b) t≠toPlane p := by
  intro he
  rcases h with h | h | h
  · have hz := realOrient_segment (toPlane a) (toPlane b) t
    rw [he,realOrient_cast] at hz
    exact h (by exact_mod_cast hz)
  · exact coordinateAvoid_ne _ _ _ _ ht0 ht1 h (congrArg Prod.fst he)
  · exact coordinateAvoid_ne _ _ _ _ ht0 ht1 h (congrArg Prod.snd he)

private theorem affine_injective (a b : Plane) (hab : a≠b) : Function.Injective (affine a b) := by
  intro s t h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [affine] at hx hy
  by_cases he : a.1=b.1
  · have hn : a.2≠b.2 := by intro he'; exact hab (Prod.ext he he')
    have hp : (s-t)*(b.2-a.2)=0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr hn.symm))
  · have hp : (s-t)*(b.1-a.1)=0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr (Ne.symm he)))

/-- All obligations are finite exact integer propositions for a finite graph. -/
structure Certificate {V E : Type} (G : MultiGraph V E) (point : V → Point) where
  injective : Function.Injective point
  nondegenerate : ∀ e,point (G.src e)≠point (G.dst e)
  separated : ∀ e f,e≠f → Separated (point (G.src e)) (point (G.dst e)) (point (G.src f)) (point (G.dst f))
  avoids : ∀ e v,Avoids (point (G.src e)) (point (G.dst e)) (point v)

def curve {V E : Type} (G : MultiGraph V E) (point : V → Point) (e : E) : C(I,Plane) where
  toFun t := affine (toPlane (point (G.src e))) (toPlane (point (G.dst e))) t
  continuous_toFun := by unfold affine; fun_prop

/-- A checked certificate constructs the actual topological plane drawing. -/
def drawing {V E : Type} {G : MultiGraph V E} {point : V → Point}
    (h : Certificate G point) : PlaneDrawing G where
  point := toPlane ∘ point
  point_injective := by
    intro v w he
    apply h.injective
    apply Prod.ext
    · have hx := congrArg Prod.fst he
      dsimp [toPlane] at hx
      exact_mod_cast hx
    · have hy := congrArg Prod.snd he
      dsimp [toPlane] at hy
      exact_mod_cast hy
  curve := curve G point
  curve_zero e := by simp [curve,affine]
  curve_one e := by simp [curve,affine]
  interior_injective := by
    intro e f s t hs ht he
    by_cases hef : e=f
    · subst f
      refine ⟨rfl,Subtype.ext ?_⟩
      apply affine_injective _ _ _ he
      intro hp
      apply h.nondegenerate e
      apply Prod.ext
      · have hx := congrArg Prod.fst hp; dsimp [toPlane] at hx; exact_mod_cast hx
      · have hy := congrArg Prod.snd hp; dsimp [toPlane] at hy; exact_mod_cast hy
    · exact False.elim (separated_ne _ _ _ _ _ _ hs.1 hs.2 ht.1 ht.2 (h.separated e f hef) he)
  interior_avoids e t ht v := avoids_ne _ _ _ _ ht.1 ht.2 (h.avoids e v)

end PlanarHom.IntegerStraightDrawing
