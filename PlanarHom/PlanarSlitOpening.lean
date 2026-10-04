import PlanarHom.PlanarRibbons
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

/-!
# An explicit opening of a straight slit

Distances to the two slit endpoints provide an Apollonius coordinate. A
stereographic coordinate along its level sets separates both sides of the slit.
Multiplication by the endpoint-vanishing factor extends continuously to both
endpoints. No plane-topology existence theorem is used in this construction.
-/

noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph
namespace SlitOpening

/-- The plane with the open horizontal unit segment removed. -/
abbrev Domain := {p : Plane // ¬ (0 < p.1 ∧ p.1 < 1 ∧ p.2 = 0)}

def leftRadius (p : Plane) : ℝ := Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
def rightRadius (p : Plane) : ℝ := Real.sqrt ((p.1 - 1) ^ 2 + p.2 ^ 2)
def radiusSum (p : Plane) : ℝ := leftRadius p + rightRadius p

def horizontal (p : Plane) : ℝ := leftRadius p / radiusSum p

def stereographic (p : Plane) : ℝ := 2 * p.2 / (radiusSum p ^ 2 - 1)
def squash (t : ℝ) : ℝ := t / (1 + |t|)
def height (p : Plane) : ℝ := horizontal p * (1 - horizontal p) *
  (1 + squash (stereographic p))

lemma leftRadius_nonneg (p : Plane) : 0 ≤ leftRadius p := Real.sqrt_nonneg _
lemma rightRadius_nonneg (p : Plane) : 0 ≤ rightRadius p := Real.sqrt_nonneg _
lemma leftRadius_sq (p : Plane) : leftRadius p ^ 2 = p.1 ^ 2 + p.2 ^ 2 :=
  Real.sq_sqrt (by positivity)
lemma rightRadius_sq (p : Plane) : rightRadius p ^ 2 = (p.1 - 1) ^ 2 + p.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma leftRadius_ge_fst (p : Plane) : p.1 ≤ leftRadius p := by
  nlinarith [leftRadius_nonneg p, leftRadius_sq p, sq_nonneg p.2]
lemma rightRadius_ge_one_sub (p : Plane) : 1 - p.1 ≤ rightRadius p := by
  nlinarith [rightRadius_nonneg p, rightRadius_sq p, sq_nonneg p.2]
lemma radiusSum_ge_one (p : Plane) : 1 ≤ radiusSum p := by
  dsimp [radiusSum]
  linarith [leftRadius_ge_fst p, rightRadius_ge_one_sub p]
lemma radiusSum_pos (p : Plane) : 0 < radiusSum p := lt_of_lt_of_le zero_lt_one (radiusSum_ge_one p)

lemma leftRadius_eq_zero (p : Plane) : leftRadius p = 0 ↔ p = (0, 0) := by
  constructor
  · intro h
    have hs := leftRadius_sq p
    rw [h] at hs
    have hx : p.1 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    have hy : p.2 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    exact Prod.ext hx hy
  · rintro rfl
    norm_num [leftRadius]
lemma rightRadius_eq_zero (p : Plane) : rightRadius p = 0 ↔ p = (1, 0) := by
  constructor
  · intro h
    have hs := rightRadius_sq p
    rw [h] at hs
    have hx : p.1 = 1 := by nlinarith [sq_nonneg (p.1 - 1), sq_nonneg p.2]
    have hy : p.2 = 0 := by nlinarith [sq_nonneg (p.1 - 1), sq_nonneg p.2]
    exact Prod.ext hx hy
  · rintro rfl
    norm_num [rightRadius]

lemma horizontal_nonneg (p : Plane) : 0 ≤ horizontal p :=
  div_nonneg (leftRadius_nonneg p) (radiusSum_pos p).le
lemma horizontal_le_one (p : Plane) : horizontal p ≤ 1 := by
  apply (div_le_one (radiusSum_pos p)).2
  dsimp [radiusSum]
  linarith [rightRadius_nonneg p]
lemma horizontal_eq_zero (p : Plane) : horizontal p = 0 ↔ p = (0, 0) := by
  rw [horizontal, div_eq_zero_iff]
  simp [(radiusSum_pos p).ne', leftRadius_eq_zero]
lemma horizontal_eq_one (p : Plane) : horizontal p = 1 ↔ p = (1, 0) := by
  rw [horizontal, div_eq_one_iff_eq (radiusSum_pos p).ne']
  simpa [radiusSum] using (rightRadius_eq_zero p)
lemma horizontal_pos {p : Plane} (h : p ≠ (0, 0)) : 0 < horizontal p :=
  lt_of_le_of_ne (horizontal_nonneg p) (Ne.symm (mt (horizontal_eq_zero p).1 h))
lemma horizontal_lt_one {p : Plane} (h : p ≠ (1, 0)) : horizontal p < 1 :=
  lt_of_le_of_ne (horizontal_le_one p) (mt (horizontal_eq_one p).1 h)

lemma radiusSum_eq_one (p : Domain) (h : radiusSum p = 1) :
    (p : Plane) = (0, 0) ∨ (p : Plane) = (1, 0) := by
  have ha : leftRadius p = p.val.1 := by
    have := leftRadius_ge_fst p
    have := rightRadius_ge_one_sub p
    dsimp [radiusSum] at h
    linarith
  have hx0 : 0 ≤ p.val.1 := by rw [← ha]; exact leftRadius_nonneg p
  have hx1 : p.val.1 ≤ 1 := by
    have := rightRadius_nonneg p
    dsimp [radiusSum] at h
    linarith
  have hy : p.val.2 = 0 := by
    have hs := leftRadius_sq p
    rw [ha] at hs
    nlinarith [sq_nonneg p.val.2]
  have hn := p.property
  by_cases hx : p.val.1 = 0
  · exact Or.inl (Prod.ext hx hy)
  · have hx' : p.val.1 = 1 := by
      by_contra hh
      exact hn ⟨lt_of_le_of_ne hx0 (Ne.symm hx), lt_of_le_of_ne hx1 hh, hy⟩
    exact Or.inr (Prod.ext hx' hy)

lemma denominator_pos {p : Domain} (h0 : (p : Plane) ≠ (0, 0))
    (h1 : (p : Plane) ≠ (1, 0)) : 0 < radiusSum p ^ 2 - 1 := by
  have hs : 1 < radiusSum p := lt_of_le_of_ne (radiusSum_ge_one p) (by
    intro h
    exact (radiusSum_eq_one p h.symm).elim h0 h1)
  nlinarith

lemma squash_bound (t : ℝ) : -1 ≤ squash t ∧ squash t ≤ 1 := by
  have hd : 0 < 1 + |t| := by positivity
  constructor
  · rw [squash, le_div_iff₀ hd]
    linarith [neg_abs_le t]
  · rw [squash, div_le_iff₀ hd]
    linarith [le_abs_self t]

lemma squash_injective : Function.Injective squash := by
  intro a b h
  have ha : 0 < 1 + |a| := by positivity
  have hb : 0 < 1 + |b| := by positivity
  have hh : a * (1 + |b|) = b * (1 + |a|) := (div_eq_div_iff ha.ne' hb.ne').1 h
  by_cases h0 : 0 ≤ a <;> by_cases h1 : 0 ≤ b
  · rw [abs_of_nonneg h0, abs_of_nonneg h1] at hh
    nlinarith
  · rw [abs_of_nonneg h0, abs_of_neg (lt_of_not_ge h1)] at hh
    have : a ≤ 0 := by nlinarith
    have : b ≥ 0 := by nlinarith
    exact False.elim (h1 this)
  · rw [abs_of_neg (lt_of_not_ge h0), abs_of_nonneg h1] at hh
    have : b ≤ 0 := by nlinarith
    have : a ≥ 0 := by nlinarith
    exact False.elim (h0 this)
  · rw [abs_of_neg (lt_of_not_ge h0), abs_of_neg (lt_of_not_ge h1)] at hh
    nlinarith

lemma height_nonneg (p : Plane) : 0 ≤ height p := by
  exact mul_nonneg (mul_nonneg (horizontal_nonneg p) (sub_nonneg.2 (horizontal_le_one p)))
    (by linarith [(squash_bound (stereographic p)).1])
lemma height_le_factor (p : Plane) : height p ≤ 2 * (horizontal p * (1 - horizontal p)) := by
  have h := (squash_bound (stereographic p)).2
  have hn := mul_nonneg (horizontal_nonneg p) (sub_nonneg.2 (horizontal_le_one p))
  dsimp [height]
  nlinarith
lemma height_le_one (p : Plane) : height p ≤ 1 := by
  have := height_le_factor p
  nlinarith [sq_nonneg (horizontal p - 1 / 2)]

@[simp] lemma horizontal_left : horizontal (0, 0) = 0 := (horizontal_eq_zero _).2 rfl
@[simp] lemma horizontal_right : horizontal (1, 0) = 1 := (horizontal_eq_one _).2 rfl
@[simp] lemma height_left : height (0, 0) = 0 := by simp [height]
@[simp] lemma height_right : height (1, 0) = 0 := by simp [height]


lemma continuous_leftRadius : Continuous leftRadius := by unfold leftRadius; fun_prop
lemma continuous_rightRadius : Continuous rightRadius := by unfold rightRadius; fun_prop
lemma continuous_radiusSum : Continuous radiusSum := continuous_leftRadius.add continuous_rightRadius
lemma continuous_horizontal : Continuous horizontal :=
  continuous_leftRadius.div continuous_radiusSum (fun p => (radiusSum_pos p).ne')
lemma continuous_squash : Continuous squash := by
  unfold squash
  exact continuous_id.div (continuous_const.add continuous_abs) (fun t => by positivity)

lemma continuousAt_height_endpoint {p : Plane} (hp : p = (0, 0) ∨ p = (1, 0)) :
    ContinuousAt height p := by
  have hz : height p = 0 := by rcases hp with rfl | rfl <;> simp
  change Filter.Tendsto height (nhds p) (nhds (height p))
  rw [hz]
  apply squeeze_zero height_nonneg height_le_factor
  have hc : Continuous (fun p : Plane => 2 * (horizontal p * (1 - horizontal p))) :=
    continuous_const.mul (continuous_horizontal.mul (continuous_const.sub continuous_horizontal))
  rcases hp with rfl | rfl
  · simpa [ContinuousAt] using hc.continuousAt (x := (0, 0))
  · simpa [ContinuousAt] using hc.continuousAt (x := (1, 0))

lemma continuous_height : Continuous (fun p : Domain => height p) := by
  apply continuous_iff_continuousAt.2
  intro p
  by_cases h0 : (p : Plane) = (0, 0)
  · exact (continuousAt_height_endpoint (Or.inl h0)).comp continuousAt_subtype_val
  by_cases h1 : (p : Plane) = (1, 0)
  · exact (continuousAt_height_endpoint (Or.inr h1)).comp continuousAt_subtype_val
  have hc : ContinuousAt stereographic (p : Plane) := by
    apply ContinuousAt.div
    · fun_prop
    · exact (continuous_radiusSum.pow 2 |>.sub continuous_const).continuousAt
    · exact (denominator_pos h0 h1).ne'
  have hh : ContinuousAt height (p : Plane) :=
    (continuous_horizontal.continuousAt.mul
      (continuous_const.continuousAt.sub continuous_horizontal.continuousAt)).mul
      (continuous_const.continuousAt.add (continuous_squash.continuousAt.comp hc))
  exact hh.comp continuousAt_subtype_val

lemma horizontal_mul_sum (p : Plane) : horizontal p * radiusSum p = leftRadius p := by
  exact div_mul_cancel₀ _ (radiusSum_pos p).ne'

lemma original_fst (p : Plane) :
    2 * p.1 = 1 + (2 * horizontal p - 1) * radiusSum p ^ 2 := by
  have hh := horizontal_mul_sum p
  have hr : (2 * horizontal p - 1) * radiusSum p = leftRadius p - rightRadius p := by
    dsimp [radiusSum] at *
    nlinarith
  calc
    2 * p.1 = 1 + (leftRadius p - rightRadius p) * radiusSum p := by
      dsimp [radiusSum]
      nlinarith [leftRadius_sq p, rightRadius_sq p]
    _ = 1 + (2 * horizontal p - 1) * radiusSum p ^ 2 := by rw [← hr]; ring

lemma ellipse_identity (p : Plane) :
    (radiusSum p ^ 2 - 1) * (1 - (2 * horizontal p - 1) ^ 2 * radiusSum p ^ 2) =
      4 * p.2 ^ 2 := by
  have hx := original_fst p
  have ha := horizontal_mul_sum p
  have hq := leftRadius_sq p
  have hh : 4 * horizontal p ^ 2 * radiusSum p ^ 2 = 4 * (p.1 ^ 2 + p.2 ^ 2) := by
    calc
      _ = 4 * (horizontal p * radiusSum p) ^ 2 := by ring
      _ = _ := by rw [ha, hq]
  linear_combination hh + (2 * p.1 + 1 + (2 * horizontal p - 1) * radiusSum p ^ 2) * hx

lemma stereographic_identity {p : Domain} (h0 : (p : Plane) ≠ (0, 0))
    (h1 : (p : Plane) ≠ (1, 0)) :
    radiusSum p ^ 2 * ((2 * horizontal p - 1) ^ 2 + stereographic p ^ 2) =
      1 + stereographic p ^ 2 := by
  have hd := denominator_pos h0 h1
  have ht : stereographic p * (radiusSum p ^ 2 - 1) = 2 * p.val.2 :=
    div_mul_cancel₀ _ hd.ne'
  have he := ellipse_identity (p : Plane)
  have ht2 : stereographic p ^ 2 * (radiusSum p ^ 2 - 1) ^ 2 = 4 * p.val.2 ^ 2 := by
    calc
      _ = (stereographic p * (radiusSum p ^ 2 - 1)) ^ 2 := by ring
      _ = _ := by rw [ht]; ring
  have hh : (radiusSum p ^ 2 - 1) *
      (1 - (2 * horizontal p - 1) ^ 2 * radiusSum p ^ 2) =
      (radiusSum p ^ 2 - 1) * (stereographic p ^ 2 * (radiusSum p ^ 2 - 1)) := by
    rw [he, ← ht2]; ring
  have hc := mul_left_cancel₀ hd.ne' hh
  nlinarith only [hc]


lemma coordinates_injective {p q : Domain}
    (hx : horizontal p = horizontal q) (hy : height p = height q) : p = q := by
  apply Subtype.ext
  by_cases hp0 : (p : Plane) = (0, 0)
  · have hq0 : (q : Plane) = (0, 0) := (horizontal_eq_zero _).1 (by rw [← hx, hp0]; simp)
    exact hp0.trans hq0.symm
  by_cases hp1 : (p : Plane) = (1, 0)
  · have hq1 : (q : Plane) = (1, 0) := (horizontal_eq_one _).1 (by rw [← hx, hp1]; simp)
    exact hp1.trans hq1.symm
  have hq0 : (q : Plane) ≠ (0, 0) := by
    intro h
    apply hp0
    apply (horizontal_eq_zero _).1
    rw [hx, h]; simp
  have hq1 : (q : Plane) ≠ (1, 0) := by
    intro h
    apply hp1
    apply (horizontal_eq_one _).1
    rw [hx, h]; simp
  have hfac : 0 < horizontal p * (1 - horizontal p) :=
    mul_pos (horizontal_pos hp0) (sub_pos.2 (horizontal_lt_one hp1))
  have ht : stereographic p = stereographic q := by
    apply squash_injective
    dsimp only [height] at hy
    rw [← hx] at hy
    exact add_left_cancel (mul_left_cancel₀ hfac.ne' hy)
  have hp := stereographic_identity hp0 hp1
  have hq := stereographic_identity hq0 hq1
  rw [← hx, ← ht] at hq
  have hc : (2 * horizontal p - 1) ^ 2 + stereographic p ^ 2 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hp
    nlinarith [sq_nonneg (stereographic p)]
  have hs2 : radiusSum p ^ 2 = radiusSum q ^ 2 := mul_right_cancel₀ hc (hp.trans hq.symm)
  have hs : radiusSum p = radiusSum q := by
    nlinarith [radiusSum_pos (p : Plane), radiusSum_pos (q : Plane)]
  apply Prod.ext
  · have hp := original_fst (p : Plane)
    have hq := original_fst (q : Plane)
    rw [← hx, ← hs] at hq
    linarith
  · dsimp only [stereographic] at ht
    rw [← hs] at ht
    have hh := (div_left_inj' (denominator_pos hp0 hp1).ne').1 ht
    linarith

/-- The explicit slit opening, with values in the closed unit square. -/
def toSquare : C(Domain, I × I) where
  toFun p := (⟨horizontal p, horizontal_nonneg p, horizontal_le_one p⟩,
    ⟨height p, height_nonneg p, height_le_one p⟩)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (continuous_horizontal.comp continuous_subtype_val).subtype_mk _
    · exact continuous_height.subtype_mk _

lemma toSquare_injective : Function.Injective toSquare := by
  intro p q h
  apply coordinates_injective
  · exact congrArg (fun x : I × I => (x.1 : ℝ)) h
  · exact congrArg (fun x : I × I => (x.2 : ℝ)) h

@[simp] lemma toSquare_left (h : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) = 0)) :
    toSquare ⟨(0, 0), h⟩ = (0, 0) := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [toSquare]

@[simp] lemma toSquare_right (h : ¬ (0 < (1 : ℝ) ∧ (1 : ℝ) < 1 ∧ (0 : ℝ) = 0)) :
    toSquare ⟨(1, 0), h⟩ = (1, 0) := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [toSquare]

lemma toSquare_inside {p : Domain} (h0 : (p : Plane) ≠ (0, 0))
    (h1 : (p : Plane) ≠ (1, 0)) : Inside (toSquare p).1 :=
  ⟨horizontal_pos h0, horizontal_lt_one h1⟩


end SlitOpening

namespace PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- A drawing avoids the open normalized segment that is to be opened. -/
def AvoidsOpenUnitSegment (d : PlaneDrawing G) : Prop :=
  ∀ p ∈ d.support, ¬ (0 < p.1 ∧ p.1 < 1 ∧ p.2 = 0)

/-- Lift a vertex into the slit domain. -/
def slitPoint (d : PlaneDrawing G) (h : d.AvoidsOpenUnitSegment) (v : V) :
    SlitOpening.Domain :=
  ⟨d.point v, h _ (Or.inl ⟨v, rfl⟩)⟩

/-- Lift an entire edge curve into the slit domain. -/
def slitCurve (d : PlaneDrawing G) (h : d.AvoidsOpenUnitSegment) (e : E) :
    C(I, SlitOpening.Domain) where
  toFun t := ⟨d.curve e t, h _ (Or.inr (mem_iUnion.2 ⟨e, ⟨t, rfl⟩⟩))⟩
  continuous_toFun := (d.curve e).continuous.subtype_mk _

@[simp] lemma slitCurve_zero (d : PlaneDrawing G) (h : d.AvoidsOpenUnitSegment) (e : E) :
    d.slitCurve h e 0 = d.slitPoint h (G.src e) :=
  Subtype.ext (d.curve_zero e)
@[simp] lemma slitCurve_one (d : PlaneDrawing G) (h : d.AvoidsOpenUnitSegment) (e : E) :
    d.slitCurve h e 1 = d.slitPoint h (G.dst e) :=
  Subtype.ext (d.curve_one e)

end PlaneDrawing
end PlanarHom.MultiGraph

namespace PlanarHom.TwoTerminal
open MultiGraph
variable {W F : Type*} {K : TwoTerminal W F}

/-- A normalized drawing disjoint from the open terminal segment gives an
actual strip drawing, through the explicit continuous injective slit opening. -/
def stripDrawingOfSlit (d : PlaneDrawing K) (h : d.AvoidsOpenUnitSegment)
    (hl : d.point (Sum.inl false) = (0, 0))
    (hr : d.point (Sum.inl true) = (1, 0)) : StripDrawing K where
  point v := SlitOpening.toSquare (d.slitPoint h v)
  point_injective := by
    intro v w he
    apply d.point_injective
    exact congrArg Subtype.val (SlitOpening.toSquare_injective he)
  left := by
    have hh : d.slitPoint h (Sum.inl false) = ⟨(0, 0), by simp⟩ := Subtype.ext hl
    rw [hh]
    exact SlitOpening.toSquare_left _
  right := by
    have hh : d.slitPoint h (Sum.inl true) = ⟨(1, 0), by simp⟩ := Subtype.ext hr
    rw [hh]
    exact SlitOpening.toSquare_right _
  internal_inside w := by
    apply SlitOpening.toSquare_inside
    · intro he
      have hh : d.point (Sum.inr w) = d.point (Sum.inl false) := he.trans hl.symm
      exact Sum.inr_ne_inl (d.point_injective hh)
    · intro he
      have hh : d.point (Sum.inr w) = d.point (Sum.inl true) := he.trans hr.symm
      exact Sum.inr_ne_inl (d.point_injective hh)
  curve e := SlitOpening.toSquare.comp (d.slitCurve h e)
  curve_zero e := by simp
  curve_one e := by simp
  curve_inside e t ht := by
    apply SlitOpening.toSquare_inside
    · intro he
      exact d.interior_avoids e t ht (Sum.inl false) (he.trans hl.symm)
    · intro he
      exact d.interior_avoids e t ht (Sum.inl true) (he.trans hr.symm)
  interior_injective e f s t hs ht he :=
    d.interior_injective e f s t hs ht
      (congrArg Subtype.val (SlitOpening.toSquare_injective he))
  interior_avoids e t ht v he :=
    d.interior_avoids e t ht v
      (congrArg Subtype.val (SlitOpening.toSquare_injective he))

end PlanarHom.TwoTerminal
