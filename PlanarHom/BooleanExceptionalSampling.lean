import PlanarHom.BooleanExceptionalPolynomial
import PlanarHom.BooleanExceptionalGrid

/-!
# Bounded rational samples separating unequal-class spectral counts

This joins actual radical-elimination certificates, analytic nonvanishing,
and the explicit rational grid. The hypotheses are only the real parameter
conditions and the finite branch-count bounds. Neither polynomial
certificates nor zero-count oracles are assumed by the final theorems.
-/
noncomputable section
open Set
open scoped BigOperators
namespace PlanarHom.BooleanExceptionalSampling
open BooleanConjugateProducts BooleanExceptionalPolynomial BooleanExceptionalGrid

/-- The original, unflipped spectral product. -/
def spectralValue {b : ℕ} (c a w : Fin b → ℝ) (n k : Fin b → ℕ) (x : ℝ) : ℝ :=
  spectralProduct Finset.univ c a w n k (fun _ => false) x

/-- The degree bound for one pair of products. -/
def degreeBound {b : ℕ} (n : Fin b → ℕ) : ℕ := 2^b * ∑ g, n g

/-- An explicit union bound over all ordered pairs of product indices. -/
def exceptionalBound (I : Type*) [Fintype I] {b : ℕ} (n : Fin b → ℕ) : ℕ :=
  Fintype.card I ^ 2 * degreeBound n

/-- Equality at this sample forces equality of all unequal-diagonal counts. -/
def SeparatesUnequalCounts {I : Type*} {b : ℕ} (c a w : Fin b → ℝ)
    (n : Fin b → ℕ) (k : I → Fin b → ℕ) (x : ℝ) : Prop :=
  ∀ i j, spectralValue c a w n (k i) x = spectralValue c a w n (k j) x →
    ∀ g, a g ≠ 0 → k i g = k j g

/-- Only pairs differing in an unequal-diagonal count are forbidden. -/
def forbiddenPairs {I : Type*} [Fintype I] {b : ℕ} (a : Fin b → ℝ)
    (k : I → Fin b → ℕ) : Finset (I × I) := by
  classical
  exact Finset.univ.filter (fun p => ∃ g, a g ≠ 0 ∧ k p.1 g ≠ k p.2 g)

@[simp] theorem mem_forbiddenPairs {I : Type*} [Fintype I] {b : ℕ}
    {a : Fin b → ℝ} {k : I → Fin b → ℕ} {p : I × I} :
    p ∈ forbiddenPairs a k ↔ ∃ g, a g ≠ 0 ∧ k p.1 g ≠ k p.2 g := by
  classical
  simp [forbiddenPairs]

theorem card_forbiddenPairs_le {I : Type*} [Fintype I] {b : ℕ}
    (a : Fin b → ℝ) (k : I → Fin b → ℕ) :
    (forbiddenPairs a k).card ≤ Fintype.card I ^ 2 := by
  classical
  simpa [forbiddenPairs, Fintype.card_prod, pow_two] using
    (Finset.card_filter_le (Finset.univ : Finset (I × I))
      (fun p => ∃ g, a g ≠ 0 ∧ k p.1 g ≠ k p.2 g))

theorem separates_iff_avoids_forbidden {I : Type*} [Fintype I] {b : ℕ}
    (c a w : Fin b → ℝ) (n : Fin b → ℕ) (k : I → Fin b → ℕ) (x : ℝ) :
    SeparatesUnequalCounts c a w n k x ↔
      ∀ p ∈ forbiddenPairs a k,
        spectralValue c a w n (k p.1) x ≠ spectralValue c a w n (k p.2) x := by
  constructor
  · intro hs p hp heq
    obtain ⟨g, hag, hkg⟩ := mem_forbiddenPairs.mp hp
    exact hkg (hs p.1 p.2 heq g hag)
  · intro hs i j heq g hag
    by_contra hkg
    exact hs (i, j) (mem_forbiddenPairs.mpr ⟨g, hag, hkg⟩) heq

/-- The concrete good samples in the grid with `B+L` rational points. -/
def separatingSamples {I : Type*} [Fintype I] {b : ℕ} (c a w : Fin b → ℝ)
    (n : Fin b → ℕ) (k : I → Fin b → ℕ) (L : ℕ) : Finset ℚ := by
  classical
  exact (rationalGrid (exceptionalBound I n + L)).filter
    (fun q => SeparatesUnequalCounts c a w n k (q : ℝ))

@[simp] theorem mem_separatingSamples {I : Type*} [Fintype I] {b : ℕ}
    {c a w : Fin b → ℝ} {n : Fin b → ℕ} {k : I → Fin b → ℕ} {L : ℕ} {q : ℚ} :
    q ∈ separatingSamples c a w n k L ↔
      q ∈ rationalGrid (exceptionalBound I n + L) ∧
        SeparatesUnequalCounts c a w n k (q : ℝ) := by
  classical
  simp [separatingSamples]

/-- At least `L` points of the explicit rational grid distinguish every
pair that differs on an unequal-diagonal parameter class. -/
theorem separatingSamples_card_ge {I : Type*} [Fintype I] {b : ℕ}
    (c a w : Fin b → ℝ) (n : Fin b → ℕ) (k : I → Fin b → ℕ) (L : ℕ)
    (hc : ∀ g, 0 < c g) (hca : ∀ g, c g^2-a g^2=1)
    (hw : ∀ g, 0 < w g) (hw1 : ∀ g, w g < 1)
    (hinj : Set.InjOn (fun g => (a g/w g)^2) {g | a g ≠ 0})
    (hk : ∀ i g, k i g ≤ n g) :
    L ≤ (separatingSamples c a w n k L).card := by
  classical
  let collision : I × I → ℚ → Prop := fun p q =>
    spectralValue c a w n (k p.1) (q : ℝ) = spectralValue c a w n (k p.2) (q : ℝ)
  let P : I × I → Polynomial ℝ := fun p => collisionPolynomial c a w n (k p.1) (k p.2)
  have hB : (forbiddenPairs a k).card * degreeBound n ≤ exceptionalBound I n :=
    Nat.mul_le_mul_right _ (card_forbiddenPairs_le a k)
  have hP : ∀ p ∈ forbiddenPairs a k, P p ≠ 0 := by
    intro p hp
    exact collisionPolynomial_ne_zero c a w n (k p.1) (k p.2)
      hc hca hw hw1 hinj (hk p.1) (hk p.2) (mem_forbiddenPairs.mp hp)
  have hdegree : ∀ p ∈ forbiddenPairs a k, (P p).natDegree ≤ degreeBound n := by
    intro p _
    exact collisionPolynomial_degree c a w n (k p.1) (k p.2) (hk p.1) (hk p.2)
  have hzero : ∀ p ∈ forbiddenPairs a k,
      ∀ q ∈ rationalGrid (exceptionalBound I n + L),
        collision p q → (P p).eval (q : ℝ) = 0 := by
    intro p _ q _ heq
    exact collisionPolynomial_eval_eq_zero c a w n (k p.1) (k p.2) (q : ℝ)
      (fun _ => false) heq
  have h := good_rationalGrid_card_ge_of_bound (forbiddenPairs a k) collision P
    (degreeBound n) (exceptionalBound I n) L hB hP hdegree hzero
  have heq : goodSamples (forbiddenPairs a k) collision
      (rationalGrid (exceptionalBound I n + L)) = separatingSamples c a w n k L := by
    ext q
    simp only [mem_goodSamples, mem_separatingSamples]
    rw [separates_iff_avoids_forbidden]
  rwa [heq] at h

/-- Exactly `L` simultaneous separating samples, with the explicit grid,
real interval and reduced rational size bounds included in the result. -/
theorem exists_separating_rational_subgrid {I : Type*} [Fintype I] {b : ℕ}
    (c a w : Fin b → ℝ) (n : Fin b → ℕ) (k : I → Fin b → ℕ) (L : ℕ)
    (hc : ∀ g, 0 < c g) (hca : ∀ g, c g^2-a g^2=1)
    (hw : ∀ g, 0 < w g) (hw1 : ∀ g, w g < 1)
    (hinj : Set.InjOn (fun g => (a g/w g)^2) {g | a g ≠ 0})
    (hk : ∀ i g, k i g ≤ n g) :
    ∃ T : Finset ℚ,
      T ⊆ rationalGrid (exceptionalBound I n + L) ∧ T.card = L ∧
      ∀ q ∈ T, (q : ℝ) ∈ Ioo (0 : ℝ) 1 ∧
        0 < q.num ∧ q.num.natAbs ≤ exceptionalBound I n + L ∧
        0 < q.den ∧ q.den ≤ exceptionalBound I n + L + 1 ∧
        SeparatesUnequalCounts c a w n k (q : ℝ) := by
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq
    (separatingSamples_card_ge c a w n k L hc hca hw hw1 hinj hk)
  have hsub : T ⊆ rationalGrid (exceptionalBound I n + L) := by
    intro q hq
    exact (mem_separatingSamples.mp (hT hq)).1
  refine ⟨T, hsub, hcard, ?_⟩
  intro q hq
  have h := subgrid_sample_bounds hsub hq
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
    (mem_separatingSamples.mp (hT hq)).2⟩

/-- Every admissible smaller-branch count vector, including repetitions
that may represent the same spectral function. -/
abbrev CountVector {b : ℕ} (n : Fin b → ℕ) := ∀ g, Fin (n g+1)

theorem card_countVector {b : ℕ} (n : Fin b → ℕ) :
    Fintype.card (CountVector n) = ∏ g, (n g+1) := by
  simp [CountVector, Fintype.card_pi]

/-- Fixedly many classes give polynomially many count vectors in the total
number of factors. -/
theorem card_countVector_le {b : ℕ} (n : Fin b → ℕ) :
    Fintype.card (CountVector n) ≤ ((∑ g, n g)+1)^b := by
  rw [card_countVector]
  calc
    (∏ g, (n g+1)) ≤ ∏ _g : Fin b, ((∑ g, n g)+1) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro g _
      exact Nat.add_le_add_right
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)) 1
    _ = ((∑ g, n g)+1)^b := by simp

/-- A displayed bound depending only on class count and total factor count. -/
def polynomialSizeBound {b : ℕ} (n : Fin b → ℕ) : ℕ :=
  (((∑ g, n g)+1)^b)^2 * (2^b * ∑ g, n g)

theorem exceptionalBound_countVector_le {b : ℕ} (n : Fin b → ℕ) :
    exceptionalBound (CountVector n) n ≤ polynomialSizeBound n := by
  exact Nat.mul_le_mul_right (degreeBound n) (Nat.pow_le_pow_left (card_countVector_le n) 2)

theorem countVector_grid_card_le {b : ℕ} (n : Fin b → ℕ) (L : ℕ) :
    (rationalGrid (exceptionalBound (CountVector n) n + L)).card ≤
      polynomialSizeBound n + L := by
  rw [card_rationalGrid]
  exact Nat.add_le_add_right (exceptionalBound_countVector_le n) L

/-- If class totals are `d_g*m`, the bound is the displayed polynomial in
`m`, of degree at most `2*b+1` for fixed class multiplicities. -/
theorem polynomialSizeBound_linear_counts {b : ℕ} (d : Fin b → ℕ) (m : ℕ) :
    polynomialSizeBound (fun g => d g*m) =
      ((((∑ g, d g)*m)+1)^b)^2 * (2^b * ((∑ g, d g)*m)) := by
  simp only [polynomialSizeBound, ← Finset.sum_mul]

/-- Simultaneous separating samples for all bounded count vectors. The
numerator and denominator bounds are explicit polynomials in the total
factor count for fixed `b`. -/
theorem exists_countVector_separating_subgrid {b : ℕ}
    (c a w : Fin b → ℝ) (n : Fin b → ℕ) (L : ℕ)
    (hc : ∀ g, 0 < c g) (hca : ∀ g, c g^2-a g^2=1)
    (hw : ∀ g, 0 < w g) (hw1 : ∀ g, w g < 1)
    (hinj : Set.InjOn (fun g => (a g/w g)^2) {g | a g ≠ 0}) :
    ∃ T : Finset ℚ,
      T ⊆ rationalGrid (exceptionalBound (CountVector n) n + L) ∧ T.card = L ∧
      ∀ q ∈ T, (q : ℝ) ∈ Ioo (0 : ℝ) 1 ∧
        0 < q.num ∧ q.num.natAbs ≤ polynomialSizeBound n + L ∧
        0 < q.den ∧ q.den ≤ polynomialSizeBound n + L + 1 ∧
        SeparatesUnequalCounts c a w n (fun k : CountVector n => fun g => (k g).val) (q : ℝ) := by
  obtain ⟨T, hsub, hcard, hT⟩ := exists_separating_rational_subgrid c a w n
    (fun k : CountVector n => fun g => (k g).val) L hc hca hw hw1 hinj
    (fun k g => Nat.le_of_lt_succ (k g).isLt)
  have hB := exceptionalBound_countVector_le n
  refine ⟨T, hsub, hcard, ?_⟩
  intro q hq
  obtain ⟨hI, hnpos, hn, hdpos, hd, hsep⟩ := hT q hq
  exact ⟨hI, hnpos, hn.trans (Nat.add_le_add_right hB L), hdpos,
    hd.trans (Nat.add_le_add_right (Nat.add_le_add_right hB L) 1), hsep⟩

end PlanarHom.BooleanExceptionalSampling
