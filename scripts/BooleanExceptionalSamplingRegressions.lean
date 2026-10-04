import PlanarHom.BooleanExceptionalSource

open scoped BigOperators
open PlanarHom.BooleanRadicalNorm PlanarHom.BooleanExceptionalPolynomial
open PlanarHom.BooleanExceptionalSource PlanarHom.BooleanConjugateProducts

-- Literal one-radical elimination of (lambda_plus-lambda_minus).
example : collisionPolynomial (fun _ : Fin 1 => (5/4 : ℝ))
    (fun _ => 3/4) (fun _ => 1/2) (fun _ => 1) (fun _ => 0) (fun _ => 1) =
    Polynomial.C (-9/4 : ℝ)-Polynomial.X^2 := by
  norm_num [collisionPolynomial, spectralTower, product, power, branchPlus, branchMinus,
    radicand, PlanarHom.BooleanRadicalNorm.norm, sub, add, mul, neg, embed, zero, radical, extend, Fin.lastCases]
  calc
    _ = -Polynomial.C ((9/16 : ℝ)*4) - Polynomial.C ((1/4 : ℝ)*4)*Polynomial.X^2 := by
      simp only [Polynomial.C_mul, map_ofNat]
      ring
    _ = _ := by norm_num

-- The generic result allows equal-diagonal classes and requires an actual
-- unequal class with changed counts for nonvanishing.
example {b : ℕ} (c a w : Fin b → ℝ) (n k l : Fin b → ℕ)
    (hp : SeparatedParameters c a w) (hk : ∀ i, k i≤n i) (hl : ∀ i, l i≤n i)
    (hdiff : ∃ g, a g≠0 ∧ k g≠l g) :
    collisionPolynomial c a w n k l≠0 :=
  collisionPolynomial_ne_zero c a w n k l hp.c_pos hp.parameter_eq hp.w_pos
    hp.w_lt_one hp.branch_inj hk hl hdiff

-- The degree is linear in product length, with a fixed dimensional constant.
example {b : ℕ} (c a w : Fin b → ℝ) (d k l : Fin b → ℕ) (m : ℕ)
    (hk : ∀ i, k i≤d i*m) (hl : ∀ i, l i≤d i*m) :
    (collisionPolynomial c a w (fun i => d i*m) k l).natDegree ≤
      (2^b*(∑ i, d i))*m := collisionPolynomial_degree_length c a w d k l m hk hl

-- Even reducible/vanishing radicands obey the exact norm zero criterion.
example (p : Tower 2) (x : ℝ) :
    (norm (fun _ => Polynomial.X^2) 2 p).eval x≠0 ↔
      ∀ σ : Fin 2 → Bool, eval 2 p x (fun _ => x) σ≠0 := by
  apply eval_norm_ne_zero_iff
  intro i
  simp

-- A fixed positive odd source exponent is proved to exist from representative
-- parameters, uniformly before the product counts are chosen.
example {b : ℕ} (θ w : Fin b → ℝ)
    (hθ : ∀ i, 1≤θ i) (hw : ∀ i, 0<w i) (hw1 : ∀ i, w i<1)
    (hrep : Function.Injective (fun i => (θ i,w i))) :
    ∃ t : ℕ, 0<t ∧ Odd t ∧ SeparatedParameters
      (fun i => PlanarHom.BooleanEigenvalueBranches.cParameter (θ i) t)
      (fun i => PlanarHom.BooleanEigenvalueBranches.aParameter (θ i) t) w :=
  exists_positive_odd_parameters θ w hθ hw hw1 hrep

-- The explicit grid includes the expected middle point and has exact size.
example : (1/2 : ℚ) ∈ PlanarHom.BooleanExceptionalGrid.rationalGrid 3 := by
  apply PlanarHom.BooleanExceptionalGrid.mem_rationalGrid_iff.mpr
  exact ⟨2,by norm_num,by norm_num,by norm_num⟩

example (N : ℕ) : (PlanarHom.BooleanExceptionalGrid.rationalGrid N).card=N :=
  PlanarHom.BooleanExceptionalGrid.card_rationalGrid N

-- Empty class families and zero factor counts make the exceptional bound zero.
example : PlanarHom.BooleanExceptionalSampling.polynomialSizeBound
    (fun i : Fin 0 => Fin.elim0 i)=0 := by
  simp [PlanarHom.BooleanExceptionalSampling.polynomialSizeBound]

example (b : ℕ) : PlanarHom.BooleanExceptionalSampling.polynomialSizeBound
    (fun _ : Fin b => 0)=0 := by
  simp [PlanarHom.BooleanExceptionalSampling.polynomialSizeBound]
