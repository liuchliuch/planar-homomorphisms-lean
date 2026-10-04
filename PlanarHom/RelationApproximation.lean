import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.ContinuousOn

/-!
# Relation-preserving rational approximation

The fixed-parameter approximation in Lemma A.4.  Integer coordinates in the
finitely generated torsion-free group spanned by the logarithms replace the
paper's equivalent rational-nullspace construction. This file proves the complete
approximation and exact relation-preservation statement. It does not formalize
the subsequent joint-availability or Turing-reduction conclusions, which rely
on Theorem A.3.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace PlanarHom.RelationApproximation

variable {ι : Type*} [Fintype ι]

/-- A finite family of real numbers has integer coordinates in a finite family,
with every integer relation reflected by its coordinates. -/
theorem exists_integer_coordinates (x : ι → ℝ) :
    ∃ (n : ℕ) (u : ι → Fin n → ℤ) (t : Fin n → ℝ),
      (∀ i, x i = ∑ j, (u i j : ℝ) * t j) ∧
      (∀ z : ι → ℤ, (∑ i, (z i : ℝ) * x i) = 0 →
        ∀ j, ∑ i, z i * u i j = 0) := by
  classical
  let S := Submodule.span ℤ (Set.range x)
  letI : Module.Finite ℤ S := Module.Finite.span_of_finite ℤ (Set.finite_range x)
  let b := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := S)
  let v (i : ι) : S := ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩
  refine ⟨b.1, (fun i => b.2.repr (v i)), (fun j => (b.2 j : ℝ)), ?_, ?_⟩
  · intro i
    have h := congrArg (fun y : S => (y : ℝ)) (b.2.sum_repr (v i))
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, zsmul_eq_mul] using h.symm
  · intro z hz j
    have hv : ∑ i, z i • v i = 0 := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Submodule.coe_zero,
        zsmul_eq_mul] using hz
    have h := congrArg (fun y : S => b.2.repr y j) hv
    simpa using h

variable {κ : Type*} [Fintype κ]

/-- Logarithms turn positive integer monomials into integer linear combinations. -/
theorem log_prod_zpow (a : ι → ℝ) (ha : ∀ i, 0 < a i) (z : ι → ℤ) :
    Real.log (∏ i, a i ^ z i) = ∑ i, (z i : ℝ) * Real.log (a i) := by
  rw [Real.log_prod _ _ (fun i _ => zpow_ne_zero _ (ne_of_gt (ha i)))]
  simp only [Real.log_zpow]

/-- Coordinate relations imply exact multiplicative relations in every positive
monomial parameterization. -/
theorem monomial_relation_of_coordinates (u : ι → κ → ℤ) (r : κ → ℝ)
    (hr : ∀ j, 0 < r j) (z : ι → ℤ)
    (hz : ∀ j, ∑ i, z i * u i j = 0) :
    ∏ i, (∏ j, r j ^ u i j) ^ z i = 1 := by
  have hp : ∀ i, 0 < ∏ j, r j ^ u i j := fun i =>
    Finset.prod_pos fun j _ => zpow_pos (hr j) _
  have hlog : Real.log (∏ i, (∏ j, r j ^ u i j) ^ z i) = 0 := by
    rw [log_prod_zpow _ hp]
    simp_rw [log_prod_zpow _ hr, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Int.cast_mul, ← Int.cast_sum, hz, Int.cast_zero,
      zero_mul, Finset.sum_const_zero]
  have h := congrArg Real.exp hlog
  rw [Real.exp_log (Finset.prod_pos fun i _ => zpow_pos (hp i) _), Real.exp_zero] at h
  exact h

/-- Every finite positive monomial chart has dense rational parameter values. -/
theorem positive_rational_monomial_approximation
    (u : ι → κ → ℤ) (t : κ → ℝ) (ht : ∀ j, 0 < t j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : κ → ℚ, (∀ j, 0 < r j) ∧
      ∀ i, |(∏ j, (r j : ℝ) ^ u i j) - ∏ j, t j ^ u i j| < δ := by
  classical
  have hpos : ∀ᶠ x : κ → ℝ in 𝓝 t, ∀ j, 0 < x j := by
    apply Filter.eventually_all.mpr
    intro j
    exact continuousAt_const.eventually_lt (continuous_apply j).continuousAt (ht j)
  have happ : ∀ᶠ x : κ → ℝ in 𝓝 t,
      ∀ i, |(∏ j, x j ^ u i j) - ∏ j, t j ^ u i j| < δ := by
    apply Filter.eventually_all.mpr
    intro i
    have hp : Tendsto (fun x : κ → ℝ => ∏ j, x j ^ u i j)
        (𝓝 t) (𝓝 (∏ j, t j ^ u i j)) := by
      apply tendsto_finset_prod
      intro j hj
      exact (continuous_apply j).continuousAt.zpow₀ (u i j) (Or.inl (ne_of_gt (ht j)))
    have hz := (hp.sub_const (∏ j, t j ^ u i j)).abs
    exact hz.eventually_lt_const (by simpa using hδ)
  have hd : DenseRange (fun r : κ → ℚ => fun j => (r j : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  obtain ⟨r, hr⟩ := hd.mem_nhds (hpos.and happ)
  refine ⟨r, ?_, hr.2⟩
  intro j
  have hj : (0 : ℝ) < (r j : ℝ) := hr.1 j
  exact_mod_cast hj

/-- Rational approximation in a monomial chart whose integer coordinates
reflect every relation among the logarithms. -/
theorem positive_approximation_of_coordinates
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (u : ι → κ → ℤ) (t : κ → ℝ)
    (hx : ∀ i, Real.log (a i) = ∑ j, (u i j : ℝ) * t j)
    (hk : ∀ z : ι → ℤ, (∑ i, (z i : ℝ) * Real.log (a i)) = 0 →
        ∀ j, ∑ i, z i * u i j = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : ι → ℚ, (∀ i, 0 < q i) ∧ (∀ i, |(q i : ℝ) - a i| < δ) ∧
      ∀ z : ι → ℤ, (∏ i, a i ^ z i) = 1 → (∏ i, q i ^ z i) = 1 := by
  classical
  have he (i : ι) : (∏ j, Real.exp (t j) ^ u i j) = a i := by
    apply Real.log_injOn_pos
      (Finset.prod_pos fun j _ => zpow_pos (Real.exp_pos _) _) (ha i)
    rw [log_prod_zpow _ (fun j => Real.exp_pos _)]
    simpa only [Real.log_exp] using (hx i).symm
  obtain ⟨r, hr, happ⟩ := positive_rational_monomial_approximation u
    (fun j => Real.exp (t j)) (fun j => Real.exp_pos _) δ hδ
  let q (i : ι) : ℚ := ∏ j, r j ^ u i j
  have hq (i : ι) : (q i : ℝ) = ∏ j, (r j : ℝ) ^ u i j := by
    simp only [q, Rat.cast_prod, Rat.cast_zpow]
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i
    exact Finset.prod_pos fun j _ => zpow_pos (hr j) _
  · intro i
    simpa only [hq i, he i] using happ i
  · intro z hz
    have hlog : (∑ i, (z i : ℝ) * Real.log (a i)) = 0 := by
      rw [← log_prod_zpow a ha, hz, Real.log_one]
    have hreal := monomial_relation_of_coordinates u (fun j => (r j : ℝ))
      (fun j => by change (0 : ℝ) < (r j : ℝ); exact_mod_cast hr j) z (hk z hlog)
    have hcast : (∏ i, (q i : ℝ) ^ z i) = 1 := by
      simpa only [hq] using hreal
    exact_mod_cast hcast


/-- Positive fixed real weights admit arbitrarily close positive rational weights
preserving every multiplicative integer relation. -/
theorem positive_relation_preserving_approximation
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : ι → ℚ, (∀ i, 0 < q i) ∧ (∀ i, |(q i : ℝ) - a i| < δ) ∧
      ∀ z : ι → ℤ, (∏ i, a i ^ z i) = 1 → (∏ i, q i ^ z i) = 1 := by
  obtain ⟨n, u, t, hx, hk⟩ := exists_integer_coordinates (fun i => Real.log (a i))
  exact positive_approximation_of_coordinates a ha u t hx hk δ hδ

/-- The approximation part of Lemma A.4: every finite nonzero real tuple has
arbitrarily close nonzero
rational tuples with the same signs that preserve all of its multiplicative
integer relations.  Extra relations in the rational tuple are allowed. -/
theorem relation_preserving_approximation
    (m : ι → ℝ) (hm : ∀ i, m i ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q : ι → ℚ, (∀ i, q i ≠ 0) ∧
      (∀ i, |(q i : ℝ) - m i| < δ) ∧
      (∀ i, Real.sign (q i : ℝ) = Real.sign (m i)) ∧
      ∀ z : ι → ℤ, (∏ i, m i ^ z i) = 1 → (∏ i, q i ^ z i) = 1 := by
  classical
  obtain ⟨p, hp, happ, hrel⟩ := positive_relation_preserving_approximation
    (fun i => |m i|) (fun i => abs_pos.mpr (hm i)) δ hδ
  let ε (i : ι) : ℚ := if m i < 0 then -1 else 1
  let q (i : ι) : ℚ := ε i * p i
  have he (i : ι) : m i = (ε i : ℝ) * |m i| := by
    by_cases h : m i < 0
    · simp [ε, h, abs_of_neg h]
    · simp [ε, h, abs_of_nonneg (le_of_not_gt h)]
  have heabs (i : ι) : |(ε i : ℝ)| = 1 := by
    dsimp [ε]
    split <;> simp
  have hq (i : ι) : (q i : ℝ) = (ε i : ℝ) * (p i : ℝ) := by
    simp only [q, Rat.cast_mul]
  have hpR (i : ι) : 0 < (p i : ℝ) := by exact_mod_cast hp i
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro i
    apply mul_ne_zero _ (ne_of_gt (hp i))
    dsimp [ε]
    split <;> simp
  · intro i
    rw [hq, he i, ← mul_sub, abs_mul, heabs, one_mul]
    exact happ i
  · intro i
    by_cases h : m i < 0
    · have hqneg : (q i : ℝ) < 0 := by
        simpa [q, ε, h] using neg_lt_zero.mpr (hpR i)
      rw [Real.sign_of_neg hqneg, Real.sign_of_neg h]
    · have hmpos : 0 < m i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (hm i))
      have hqpos : 0 < (q i : ℝ) := by simpa [q, ε, h] using hpR i
      rw [Real.sign_of_pos hqpos, Real.sign_of_pos hmpos]
  · intro z hz
    have habs : (∏ i, |m i| ^ z i) = 1 := by
      have hab := congrArg abs hz
      have habspow (a : ℝ) (k : ℤ) : |a ^ k| = |a| ^ k :=
        map_zpow₀ (absHom : ℝ →*₀ ℝ) a k
      simpa only [Finset.abs_prod, habspow, abs_one] using hab
    have hεreal : (∏ i, (ε i : ℝ) ^ z i) = 1 := by
      have h : (∏ i, (ε i : ℝ) ^ z i) * (∏ i, |m i| ^ z i) = 1 := by
        calc
          _ = ∏ i, ((ε i : ℝ) * |m i|) ^ z i := by
            simp only [mul_zpow, Finset.prod_mul_distrib]
          _ = ∏ i, m i ^ z i := by simp only [← he]
          _ = 1 := hz
      simpa only [habs, mul_one] using h
    have hε : (∏ i, ε i ^ z i) = 1 := by exact_mod_cast hεreal
    dsimp only [q]
    simp only [mul_zpow, Finset.prod_mul_distrib, hε, hrel z habs, one_mul]

/-- Exact integer-relation preservation also preserves equality of arbitrary
integer monomials.  Taking nonnegative exponents gives the equal-products
implication used in the matrix replacement argument. -/
theorem prod_eq_of_preserves_integer_relations
    (m : ι → ℝ) (q : ι → ℚ) (hm : ∀ i, m i ≠ 0) (hq : ∀ i, q i ≠ 0)
    (hrel : ∀ z : ι → ℤ, (∏ i, m i ^ z i) = 1 → (∏ i, q i ^ z i) = 1)
    (z w : ι → ℤ) (h : (∏ i, m i ^ z i) = ∏ i, m i ^ w i) :
    (∏ i, q i ^ z i) = ∏ i, q i ^ w i := by
  have hmprod : (∏ i, m i ^ w i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (hm i))
  have hqprod : (∏ i, q i ^ w i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (hq i))
  have hmrel : (∏ i, m i ^ (z i - w i)) = 1 := by
    simp_rw [zpow_sub₀ (hm _), Finset.prod_div_distrib]
    rw [h, div_self hmprod]
  have hqrel := hrel (fun i => z i - w i) hmrel
  simp_rw [zpow_sub₀ (hq _), Finset.prod_div_distrib] at hqrel
  exact (div_eq_one_iff_eq hqprod).mp hqrel

end PlanarHom.RelationApproximation
