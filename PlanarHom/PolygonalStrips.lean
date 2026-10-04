import PlanarHom.PlanarPolygonalDrawing

/-!
# Explicit bilinear polygonal strips

A quadrilateral strip is given by an explicit polynomial formula. Four finite
planar determinant inequalities prove injectivity on its longitudinal interior,
including the cases where exactly one endpoint cross-section is pinched.
-/

noncomputable section
open Set unitInterval
namespace PlanarHom.Polygonal
open MultiGraph

/-- The oriented planar determinant. -/
def cross (u v : Plane) : ℝ := u.1 * v.2 - u.2 * v.1

@[simp] theorem cross_self (u : Plane) : cross u u = 0 := by unfold cross; ring
@[simp] theorem cross_zero_left (u : Plane) : cross 0 u = 0 := by simp [cross]
@[simp] theorem cross_zero_right (u : Plane) : cross u 0 = 0 := by simp [cross]
@[simp] theorem cross_add_left (u v w : Plane) : cross (u + v) w = cross u w + cross v w := by
  simp only [cross, Prod.fst_add, Prod.snd_add]; ring
@[simp] theorem cross_add_right (u v w : Plane) : cross u (v + w) = cross u v + cross u w := by
  simp only [cross, Prod.fst_add, Prod.snd_add]; ring
@[simp] theorem cross_smul_left (c : ℝ) (u v : Plane) : cross (c • u) v = c * cross u v := by
  simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
@[simp] theorem cross_smul_right (c : ℝ) (u v : Plane) : cross u (c • v) = c * cross u v := by
  simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

@[simp] theorem cross_neg_left (u v : Plane) : cross (-u) v = -cross u v := by
  simp only [cross, Prod.fst_neg, Prod.snd_neg]; ring
@[simp] theorem cross_neg_right (u v : Plane) : cross u (-v) = -cross u v := by
  simp only [cross, Prod.fst_neg, Prod.snd_neg]; ring

/-- Linearly interpolate both the center segment and its transverse cross-section. -/
def strip (P Q A B : Plane) (t s : ℝ) : Plane :=
  P + t • (Q - P) + s • (A + t • (B - A))

/-- The same explicit formula as a continuous closed-square map. -/
def stripMap (P Q A B : Plane) : C(I × I, Plane) where
  toFun p := strip P Q A B p.1 p.2
  continuous_toFun := by unfold strip; fun_prop

@[simp] theorem strip_zero (P Q A B : Plane) (s : ℝ) : strip P Q A B 0 s = P + s • A := by
  simp [strip]

@[simp] theorem strip_one (P Q A B : Plane) (s : ℝ) : strip P Q A B 1 s = Q + s • B := by
  unfold strip
  module

@[simp] theorem stripMap_pinched_zero (P Q B : Plane) (s : I) :
    stripMap P Q 0 B (0, s) = P := by simp [stripMap]

@[simp] theorem stripMap_pinched_one (P Q A : Plane) (s : I) :
    stripMap P Q A 0 (1, s) = Q := by simp [stripMap]

/-- The exact difference formula used to prove global, not only local, injectivity. -/
theorem strip_sub (P Q A B : Plane) (t s u v : ℝ) :
    strip P Q A B t s - strip P Q A B u v =
      (t - u) • (Q - P + s • (B - A)) +
      (s - v) • (A + u • (B - A)) := by
  unfold strip
  module

/-- Strict positivity of the mixed determinant gives genuine strip injectivity. -/
theorem stripMap_injective_of_cross_pos (P Q A B : Plane)
    (hcross : ∀ u : ℝ, 0 < u → u < 1 → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      0 < cross (Q - P + s • (B - A)) (A + u • (B - A)))
    (p q : I × I) (hp : Inside p.1) (hq : Inside q.1)
    (heq : stripMap P Q A B p = stripMap P Q A B q) : p = q := by
  let D := Q - P + (p.2 : ℝ) • (B - A)
  let N := A + (q.1 : ℝ) • (B - A)
  have hpos : 0 < cross D N := hcross q.1 hq.1 hq.2 p.2 p.2.2.1 p.2.2.2
  have hz : ((p.1 : ℝ) - (q.1 : ℝ)) • D + ((p.2 : ℝ) - (q.2 : ℝ)) • N = 0 := by
    rw [← strip_sub]
    exact sub_eq_zero.mpr heq
  have ht : ((p.1 : ℝ) - (q.1 : ℝ)) * cross D N = 0 := by
    simpa using congrArg (fun W => cross W N) hz
  have hs : ((p.2 : ℝ) - (q.2 : ℝ)) * cross D N = 0 := by
    simpa using congrArg (fun W => cross D W) hz
  apply Prod.ext <;> apply Subtype.ext
  · exact sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right (ne_of_gt hpos))
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right (ne_of_gt hpos))

/-- A strictly interior convex combination is positive if either nonnegative
endpoint value is positive. -/
theorem interior_combo_pos {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpos : 0 < a ∨ 0 < b) (hu : 0 < u) (hu1 : u < 1) :
    0 < (1 - u) * a + u * b := by
  rcases hpos with ha' | hb'
  · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) ha') (mul_nonneg hu.le hb)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) ha) (mul_pos hu hb')

/-- A closed convex combination of two positive numbers is positive. -/
theorem closed_combo_pos {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : 0 < (1 - s) * a + s * b := by
  by_cases he : s = 1
  · simpa only [he, sub_self, zero_mul, one_mul, zero_add] using hb
  · have hslt : s < 1 := lt_of_le_of_ne hs1 he
    exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) ha) (mul_nonneg hs hb.le)

/-- The mixed determinant is the interpolation of its four corner values. -/
theorem cross_strip_corners (D A B : Plane) (u s : ℝ) :
    cross (D + s • (B - A)) (A + u • (B - A)) =
      (1 - s) * ((1 - u) * cross D A + u * cross D B) +
      s * ((1 - u) * cross (D + (B - A)) A + u * cross (D + (B - A)) B) := by
  simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Four explicit nonnegative corner determinants, with positivity in each
longitudinal pair, suffice even when one cross-section is pinched to a point. -/
theorem stripMap_injective_of_corner_signs (P Q A B : Plane)
    (h00 : 0 ≤ cross (Q - P) A) (h10 : 0 ≤ cross (Q - P) B)
    (h01 : 0 ≤ cross (Q - P + (B - A)) A)
    (h11 : 0 ≤ cross (Q - P + (B - A)) B)
    (hbottom : 0 < cross (Q - P) A ∨ 0 < cross (Q - P) B)
    (htop : 0 < cross (Q - P + (B - A)) A ∨ 0 < cross (Q - P + (B - A)) B)
    (p q : I × I) (hp : Inside p.1) (hq : Inside q.1)
    (heq : stripMap P Q A B p = stripMap P Q A B q) : p = q := by
  apply stripMap_injective_of_cross_pos P Q A B ?_ p q hp hq heq
  intro u hu hu1 s hs hs1
  rw [cross_strip_corners]
  exact closed_combo_pos (interior_combo_pos h00 h10 hbottom hu hu1)
    (interior_combo_pos h01 h11 htop hu hu1) hs hs1

/-- A straight strip pinched at its initial endpoint is embedded on every
longitudinal interior, with arbitrary positive transverse determinant. -/
theorem stripMap_pinched_start_injective (P Q B : Plane)
    (h : 0 < cross (Q - P) B) (p q : I × I) (hp : Inside p.1) (hq : Inside q.1)
    (heq : stripMap P Q 0 B p = stripMap P Q 0 B q) : p = q := by
  apply stripMap_injective_of_corner_signs P Q 0 B (by simp) (le_of_lt h)
    (by simp) (by simpa using h.le) (Or.inr h) (by simpa using h) p q hp hq heq

/-- The terminally pinched version follows from the same global calculation. -/
theorem stripMap_pinched_end_injective (P Q A : Plane)
    (h : 0 < cross (Q - P) A) (p q : I × I) (hp : Inside p.1) (hq : Inside q.1)
    (heq : stripMap P Q A 0 p = stripMap P Q A 0 q) : p = q := by
  apply stripMap_injective_of_corner_signs P Q A 0 h.le (by simp)
    (by simpa using h.le) (by simp)
    (Or.inl h) (by simpa using h) p q hp hq heq


@[simp] theorem cross_sub_left (u v w : Plane) : cross (u - v) w = cross u w - cross v w := by
  simp [sub_eq_add_neg]
@[simp] theorem cross_sub_right (u v w : Plane) : cross u (v - w) = cross u v - cross u w := by
  simp [sub_eq_add_neg]
theorem cross_swap (u v : Plane) : cross u v = -cross v u := by
  unfold cross
  ring

/-- Interpolate the signed side of any fixed cross-section. -/
theorem cross_interpolate (D M N : Plane) (s : ℝ) :
    cross (D + s • M) N = (1 - s) * cross D N + s * cross (D + M) N := by
  simp only [cross_add_left, cross_smul_left]
  ring

/-- A strip lies on the negative side of its initial transverse line. -/
theorem strip_cross_start (P Q A B : Plane) (t s : ℝ) :
    cross A (strip P Q A B t s - P) =
      -t * cross (Q - P + s • (B - A)) A := by
  simp only [strip, cross_add_right, cross_sub_right, cross_smul_right, cross_self,
    cross_add_left, cross_sub_left, cross_smul_left]
  rw [cross_swap A Q, cross_swap A P, cross_swap A B]
  ring

/-- A strip lies on the positive side of its terminal transverse line. -/
theorem strip_cross_end (P Q A B : Plane) (t s : ℝ) :
    cross B (strip P Q A B t s - Q) =
      (1 - t) * cross (Q - P + s • (B - A)) B := by
  simp only [strip, cross_add_right, cross_sub_right, cross_smul_right, cross_self,
    cross_add_left, cross_sub_left, cross_smul_left]
  rw [cross_swap B Q, cross_swap B P, cross_swap B A]
  ring

/-- Adjacent strips with one common transverse cross-section meet precisely
there. The two longitudinal parameters are forced to their touching endpoints,
and the transverse parameters agree. -/
theorem adjacent_strip_intersection (P Q R A N B : Plane)
    (hP0 : 0 < cross (Q - P) N) (hP1 : 0 < cross (Q - P + (N - A)) N)
    (hQ0 : 0 < cross (R - Q) N) (hQ1 : 0 < cross (R - Q + (B - N)) N)
    (p q : I × I) (heq : stripMap P Q A N p = stripMap Q R N B q) :
    p.1 = 1 ∧ q.1 = 0 ∧ p.2 = q.2 := by
  let J := cross (Q - P + (p.2 : ℝ) • (N - A)) N
  let K := cross (R - Q + (q.2 : ℝ) • (B - N)) N
  have hJ : 0 < J := by
    dsimp only [J]
    rw [cross_interpolate]
    exact closed_combo_pos hP0 hP1 p.2.2.1 p.2.2.2
  have hK : 0 < K := by
    dsimp only [K]
    rw [cross_interpolate]
    exact closed_combo_pos hQ0 hQ1 q.2.2.1 q.2.2.2
  have hc := congrArg (fun Z : Plane => cross N (Z - Q)) heq
  change cross N (strip P Q A N p.1 p.2 - Q) =
    cross N (strip Q R N B q.1 q.2 - Q) at hc
  rw [strip_cross_end, strip_cross_start] at hc
  change (1 - (p.1 : ℝ)) * J = -(q.1 : ℝ) * K at hc
  have hj0 : (1 - (p.1 : ℝ)) * J = 0 := by
    have hleft := mul_nonneg (sub_nonneg.mpr p.1.2.2) hJ.le
    have hright := mul_nonneg q.1.2.1 hK.le
    nlinarith
  have hk0 : (q.1 : ℝ) * K = 0 := by nlinarith [hj0]
  have hpval : (p.1 : ℝ) = 1 := by
    have := (mul_eq_zero.mp hj0).resolve_right (ne_of_gt hJ)
    linarith
  have hqval : (q.1 : ℝ) = 0 :=
    (mul_eq_zero.mp hk0).resolve_right (ne_of_gt hK)
  have hp1 : p.1 = 1 := Subtype.ext hpval
  have hq0 : q.1 = 0 := Subtype.ext hqval
  refine ⟨hp1, hq0, ?_⟩
  change strip P Q A N p.1 p.2 = strip Q R N B q.1 q.2 at heq
  rw [hpval, hqval, strip_one, strip_zero] at heq
  have htrans := congrArg (fun Z : Plane => cross (Q - P) (Z - Q)) heq
  simp only [add_sub_cancel_left, cross_smul_right] at htrans
  apply Subtype.ext
  exact mul_right_cancel₀ (ne_of_gt hP0) htrans

end PlanarHom.Polygonal
