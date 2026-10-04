import PlanarHom.BooleanExceptionalSampling

/-!
# Source-parameter specialization of the explicit collision certificates

A single positive odd exponent is chosen from the actual parameter pairs.
At that fixed exponent every unequal-class count collision admits the
constructed nonzero polynomial certificate and the linear degree bound.
-/
noncomputable section
open scoped BigOperators
namespace PlanarHom.BooleanExceptionalSource
open BooleanEigenvalueBranches BooleanParameterSeparation BooleanRatioIndependence
open BooleanExceptionalPolynomial BooleanConjugateProducts

/-- The numerical hypotheses already proved for the source eigenbranches. -/
structure SeparatedParameters {b : ℕ} (c a w : Fin b → ℝ) : Prop where
  c_pos : ∀ i, 0<c i
  parameter_eq : ∀ i, c i^2-a i^2=1
  w_pos : ∀ i, 0<w i
  w_lt_one : ∀ i, w i<1
  branch_inj : Set.InjOn (fun i => (a i/w i)^2) {i | a i≠0}

/-- The fixed exponent is derived from the actual representative parameters,
not supplied as an effective nonvanishing or separation oracle. -/
theorem exists_positive_odd_parameters {b : ℕ} (θ w : Fin b → ℝ)
    (hθ : ∀ i, 1≤θ i) (hw : ∀ i, 0<w i) (hw1 : ∀ i, w i<1)
    (hrep : Function.Injective (fun i => (θ i,w i))) :
    ∃ t : ℕ, 0<t ∧ Odd t ∧
      SeparatedParameters (fun i => cParameter (θ i) t) (fun i => aParameter (θ i) t) w := by
  obtain ⟨t, ht, ho, _, hinj⟩ := exists_positive_odd_representatives Finset.univ θ w
    (fun i _ => hw i) (fun _ _ _ _ h => hrep h)
  refine ⟨t, ht, ho, ?_⟩
  refine ⟨fun i => cParameter_pos (lt_of_lt_of_le zero_lt_one (hθ i)) t,
    fun i => parameter_identity _ _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (hθ i))),
    hw, hw1, ?_⟩
  intro i hi j hj heq
  have hθi := (aParameter_ne_zero_iff (hθ i) ht).mp hi
  have hθj := (aParameter_ne_zero_iff (hθ j) ht).mp hj
  apply hinj ⟨Finset.mem_univ i,hθi⟩ ⟨Finset.mem_univ j,hθj⟩
  dsimp only at heq ⊢
  rw [aParameter_div_eq_beta,aParameter_div_eq_beta] at heq
  have hbi := beta_pos hθi (hw i) ht
  have hbj := beta_pos hθj (hw j) ht
  nlinarith

/-- The source's fixed odd exponent works simultaneously for all finite
product lengths and count vectors. Its degree bound is `2^b * totalFactors`.
The root implication concerns the actual positive-square-root branches. -/
theorem exists_positive_odd_collisionCertificates {b : ℕ} (θ w : Fin b → ℝ)
    (hθ : ∀ i, 1≤θ i) (hw : ∀ i, 0<w i) (hw1 : ∀ i, w i<1)
    (hrep : Function.Injective (fun i => (θ i,w i))) :
    ∃ t : ℕ, 0<t ∧ Odd t ∧ ∀ n k l : Fin b → ℕ,
      (∀ i, k i≤n i) → (∀ i, l i≤n i) →
      (∃ g, 1<θ g ∧ k g≠l g) →
      let c := fun i => cParameter (θ i) t
      let a := fun i => aParameter (θ i) t
      collisionPolynomial c a w n k l≠0 ∧
        (collisionPolynomial c a w n k l).natDegree≤2^b*(∑ i, n i) ∧
        ∀ (x : ℝ) (σ : Fin b → Bool),
          spectralProduct Finset.univ c a w n k σ x =
            spectralProduct Finset.univ c a w n l σ x →
          (collisionPolynomial c a w n k l).eval x=0 := by
  obtain ⟨t,ht,ho,hp⟩ := exists_positive_odd_parameters θ w hθ hw hw1 hrep
  refine ⟨t,ht,ho,?_⟩
  intro n k l hk hl hdiff
  refine ⟨collisionPolynomial_ne_zero _ _ _ _ _ _ hp.c_pos hp.parameter_eq hp.w_pos
    hp.w_lt_one hp.branch_inj hk hl ?_, collisionPolynomial_degree _ _ _ _ _ _ hk hl,
    fun x σ heq => collisionPolynomial_eval_eq_zero _ _ _ _ _ _ x σ heq⟩
  obtain ⟨g,hg,hkl⟩ := hdiff
  exact ⟨g, ne_of_gt (aParameter_pos hg ht),hkl⟩

/-- With class multiplicities `d_i` and `m` selected eigenvalues, the degree
is at most the explicit constant `2^b * (sum d_i)` times `m`. -/
theorem collisionPolynomial_degree_length {b : ℕ} (c a w : Fin b → ℝ)
    (d k l : Fin b → ℕ) (m : ℕ)
    (hk : ∀ i, k i≤d i*m) (hl : ∀ i, l i≤d i*m) :
    (collisionPolynomial c a w (fun i => d i*m) k l).natDegree ≤
      (2^b*(∑ i, d i))*m := by
  simpa only [← Finset.sum_mul, Nat.mul_assoc] using
    collisionPolynomial_degree c a w (fun i => d i*m) k l hk hl

/-- The source parameters themselves admit polynomially bounded simultaneous
rational grids after one fixed positive odd exponent has been chosen. The
sample property refers directly to `theta > 1` for each unequal class. -/
theorem exists_positive_odd_separatingGrids {I : Type*} [Fintype I] {b : ℕ}
    (θ w : Fin b → ℝ) (hθ : ∀ i, 1≤θ i) (hw : ∀ i, 0<w i) (hw1 : ∀ i, w i<1)
    (hrep : Function.Injective (fun i => (θ i,w i))) :
    ∃ t : ℕ, 0<t ∧ Odd t ∧ ∀ (n : Fin b → ℕ) (k : I → Fin b → ℕ) (L : ℕ),
      (∀ i g, k i g≤n g) →
      let c := fun i => cParameter (θ i) t
      let a := fun i => aParameter (θ i) t
      let B := BooleanExceptionalSampling.exceptionalBound I n
      ∃ T : Finset ℚ,
        T ⊆ BooleanExceptionalGrid.rationalGrid (B+L) ∧ T.card=L ∧
        ∀ q∈T, (q : ℝ)∈Set.Ioo (0 : ℝ) 1 ∧
          0<q.num ∧ q.num.natAbs≤B+L ∧ 0<q.den ∧ q.den≤B+L+1 ∧
          ∀ i j, BooleanExceptionalSampling.spectralValue c a w n (k i) (q : ℝ) =
            BooleanExceptionalSampling.spectralValue c a w n (k j) (q : ℝ) →
            ∀ g, 1<θ g → k i g=k j g := by
  obtain ⟨t,ht,ho,hp⟩ := exists_positive_odd_parameters θ w hθ hw hw1 hrep
  refine ⟨t,ht,ho,?_⟩
  intro n k L hk
  obtain ⟨T,hT,hcard,hgood⟩ := BooleanExceptionalSampling.exists_separating_rational_subgrid
    _ _ _ n k L hp.c_pos hp.parameter_eq hp.w_pos hp.w_lt_one hp.branch_inj hk
  refine ⟨T,hT,hcard,?_⟩
  intro q hq
  have h := hgood q hq
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_⟩
  intro i j heq g hg
  exact h.2.2.2.2.2 i j heq g (ne_of_gt (aParameter_pos hg ht))

/-- A single positive odd source exponent works for the entire polynomially
bounded rectangle of class counts, for every product length. -/
theorem exists_positive_odd_countVectorGrids {b : ℕ}
    (θ w : Fin b → ℝ) (hθ : ∀ i, 1≤θ i) (hw : ∀ i, 0<w i) (hw1 : ∀ i, w i<1)
    (hrep : Function.Injective (fun i => (θ i,w i))) :
    ∃ t : ℕ, 0<t ∧ Odd t ∧ ∀ (n : Fin b → ℕ) (L : ℕ),
      let c := fun i => cParameter (θ i) t
      let a := fun i => aParameter (θ i) t
      let B := BooleanExceptionalSampling.exceptionalBound
        (BooleanExceptionalSampling.CountVector n) n
      let P := BooleanExceptionalSampling.polynomialSizeBound n
      ∃ T : Finset ℚ,
        T ⊆ BooleanExceptionalGrid.rationalGrid (B+L) ∧ T.card=L ∧ B≤P ∧
        ∀ q∈T, (q : ℝ)∈Set.Ioo (0 : ℝ) 1 ∧
          0<q.num ∧ q.num.natAbs≤P+L ∧ 0<q.den ∧ q.den≤P+L+1 ∧
          ∀ u v : BooleanExceptionalSampling.CountVector n,
            BooleanExceptionalSampling.spectralValue c a w n (fun i => (u i).val) (q : ℝ) =
            BooleanExceptionalSampling.spectralValue c a w n (fun i => (v i).val) (q : ℝ) →
            ∀ g, 1<θ g → u g=v g := by
  obtain ⟨t,ht,ho,hp⟩ := exists_positive_odd_parameters θ w hθ hw hw1 hrep
  refine ⟨t,ht,ho,?_⟩
  intro n L
  obtain ⟨T,hT,hcard,hgood⟩ := BooleanExceptionalSampling.exists_countVector_separating_subgrid
    _ _ _ n L hp.c_pos hp.parameter_eq hp.w_pos hp.w_lt_one hp.branch_inj
  refine ⟨T,hT,hcard,BooleanExceptionalSampling.exceptionalBound_countVector_le n,?_⟩
  intro q hq
  have h := hgood q hq
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_⟩
  intro u v heq g hg
  exact Fin.ext (h.2.2.2.2.2 u v heq g (ne_of_gt (aParameter_pos hg ht)))

end PlanarHom.BooleanExceptionalSource
