import PlanarHom.BooleanRatioIndependence
import Mathlib.Tactic.FinCases

noncomputable section
open Set
open scoped BigOperators
open PlanarHom.BooleanRatioIndependence PlanarHom.BooleanEigenvalueBranches
open PlanarHom.BooleanParameterSeparation

private def θ : Fin 3 → ℝ := ![1,2,3]
private def w : Fin 3 → ℝ := fun _ => 1/2

-- A genuine equal-diagonal class coexists with two separated unequal classes.
-- The integer exponent vector is arbitrary and can have negative entries.
example (z : Fin 3 → ℤ)
    (hid : ∀ x ∈ Ioo (0 : ℝ) 1, ∏ i : Fin 3, delta (θ i) (w i) 1 x ^ z i = 1) :
    z 1 = 0 ∧ z 2 = 0 := by
  have hθ : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 1 ≤ θ i := by
    intro i hi
    fin_cases i <;> norm_num [θ]
  have hβ : Set.InjOn (fun i => beta (θ i) (w i) 1)
      {i | i ∈ (Finset.univ : Finset (Fin 3)) ∧ 1 < θ i} := by
    intro i hi j hj heq
    fin_cases i <;> fin_cases j <;> norm_num [θ,w,beta] at *
  have h := source_ratio_identity Finset.univ θ w 1 z (by norm_num) hθ
    (by intro i hi; norm_num [w]) (by intro i hi; norm_num [w]) hβ hid
  exact ⟨h 1 (Finset.mem_univ _) (by change (1 : ℝ) < 2; norm_num),
    h 2 (Finset.mem_univ _) (by change (1 : ℝ) < 3; norm_num)⟩

-- Equal-diagonal factors really can cancel with signed nonzero exponents;
-- the theorem correctly imposes no zero-exponent conclusion on this class.
example (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    delta 1 (1/2) 1 x ^ (1 : ℤ) * delta 1 (1/2) 1 x ^ (-1 : ℤ) = 1 := by
  have hp : 0 < ratio 1 0 (1/2) (x^2) := by
    exact (branches_positive 1 0 (1/2) (x^2) (by norm_num) (by norm_num)
      (by nlinarith [sq_pos_of_pos hx.1])
      (PlanarHom.BooleanRatioParity.square_parameter_bounds (by norm_num) (by norm_num)
        ⟨by linarith [hx.1], hx.2⟩)).2.2.1
  have hd : delta 1 (1/2) 1 x ≠ 0 := by
    simpa only [delta,cParameter_one,aParameter_one] using ne_of_gt hp
  simpa only [zpow_one, zpow_neg_one] using mul_inv_cancel₀ hd

-- A nonzero single unequal-diagonal exponent cannot give the constant1
-- function, even for a negative exponent.
example : ¬(∀ x ∈ Ioo (0 : ℝ) 1, delta 2 (1/2) 1 x ^ (-3 : ℤ) = 1) := by
  intro hid
  have h := source_ratio_identity ({()} : Finset Unit) (fun _ : Unit => 2)
    (fun _ : Unit => 1/2) 1 (fun _ : Unit => -3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i hi j hj heq; exact Subsingleton.elim _ _)
    (by simpa using hid) () (by simp) (by norm_num)
  norm_num at h
