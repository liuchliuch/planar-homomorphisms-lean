import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Perfect
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Real.Archimedean

/-! # Fixed rational sign intervals around algebraic real constants

Separability supplies a simple root. Factoring out its real linear factor and
using continuity gives a rational interval on which a fixed rational polynomial
has precisely the sign of `t-a`. Only fixed program data is selected here.
-/

noncomputable section
namespace PlanarHom.AlgebraicRealSignInterval
open Polynomial

theorem interval_of_positive_factor (p : ℚ[X]) (q : ℝ[X]) (a : ℝ)
    (hp : p.map (algebraMap ℚ ℝ) = (X-C a)*q) (hq : 0 < q.eval a) :
    ∃ l u : ℚ, (l:ℝ) < a ∧ a < (u:ℝ) ∧
      ∀ t : ℚ, l ≤ t → t ≤ u → (0 ≤ p.eval t ↔ a ≤ (t:ℝ)) := by
  have hpos : ∀ᶠ t in nhds a, 0 < q.eval t :=
    continuousAt_const.eventually_lt q.continuousAt hq
  obtain ⟨δ, hδ, hδq⟩ := Metric.eventually_nhds_iff.mp hpos
  obtain ⟨l, hla, hla'⟩ := exists_rat_btwn (show a-δ < a by linarith)
  obtain ⟨u, hau, hau'⟩ := exists_rat_btwn (show a < a+δ by linarith)
  refine ⟨l, u, hla', hau, ?_⟩
  intro t ht ht'
  have htl : (l:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have htu : (t:ℝ) ≤ (u:ℝ) := by exact_mod_cast ht'
  have hdist : dist (t:ℝ) a < δ := by rw [Real.dist_eq]; apply abs_lt.mpr; constructor <;> linarith
  have hqt : 0 < q.eval (t:ℝ) := hδq hdist
  have he : ((p.eval t : ℚ):ℝ) = ((t:ℝ)-a)*q.eval (t:ℝ) := by
    change (algebraMap ℚ ℝ) (p.eval t) = _
    rw [← Polynomial.eval₂_at_apply (algebraMap ℚ ℝ), ← Polynomial.eval_map, hp]
    simp
  rw [← Rat.cast_nonneg (K:=ℝ), he, mul_nonneg_iff_of_pos_right hqt, sub_nonneg]

theorem exists_sign_interval (a : ℝ) (ha : IsAlgebraic ℚ a) :
    ∃ p : ℚ[X], ∃ l u : ℚ, (l:ℝ) < a ∧ a < (u:ℝ) ∧
      ∀ t : ℚ, l ≤ t → t ≤ u → (0 ≤ p.eval t ↔ a ≤ (t:ℝ)) := by
  let p := minpoly ℚ a
  let P := p.map (algebraMap ℚ ℝ)
  have hr : P.IsRoot a := by
    change P.eval a = 0
    simpa [P, p, Polynomial.eval_map, Polynomial.aeval_def] using minpoly.aeval ℚ a
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hr
  have hs : p.Separable := (minpoly.irreducible ha.isIntegral).separable
  have hd : P.derivative.eval a ≠ 0 := by
    simpa [P, Polynomial.derivative_map, Polynomial.eval_map, Polynomial.aeval_def] using
      hs.aeval_derivative_ne_zero (minpoly.aeval ℚ a)
  have hqa : q.eval a ≠ 0 := by
    simpa [hq, Polynomial.derivative_mul] using hd
  rcases lt_or_gt_of_ne hqa with hn | hp
  · have hmap : (-p).map (algebraMap ℚ ℝ) = (X-C a)*(-q) := by
      rw [Polynomial.map_neg]
      change -P = _
      rw [hq]
      ring
    obtain ⟨l, u, hl, hu, ht⟩ := interval_of_positive_factor (-p) (-q) a hmap (by simpa using neg_pos.mpr hn)
    exact ⟨-p, l, u, hl, hu, ht⟩
  · obtain ⟨l, u, hl, hu, ht⟩ := interval_of_positive_factor p q a hq hp
    exact ⟨p, l, u, hl, hu, ht⟩

end PlanarHom.AlgebraicRealSignInterval
