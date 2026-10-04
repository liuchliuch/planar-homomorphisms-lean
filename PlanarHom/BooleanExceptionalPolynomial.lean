import PlanarHom.BooleanRadicalNorm
import PlanarHom.BooleanConjugateProducts
import PlanarHom.PolynomialProductZeros

/-!
# Actual polynomial certificates for unequal-class spectral collisions

The certificates are obtained by explicit elimination of the square roots.
Their degree is linear in the total factor count for a fixed class set. Their
nonvanishing follows from the genuine ratio-independence theorem, and is not
an input hypothesis.
-/
noncomputable section
open scoped BigOperators
open Set
namespace PlanarHom.BooleanExceptionalPolynomial
open BooleanRadicalNorm BooleanConjugateProducts

/-- Extend the finite parameter family only to simplify the recursive tower. -/
def extend {b : ℕ} (f : Fin b → ℝ) (i : ℕ) : ℝ :=
  if h : i<b then f ⟨i,h⟩ else 0

@[simp] theorem extend_val {b : ℕ} (f : Fin b → ℝ) (i : Fin b) :
    extend f i.val=f i := by simp [extend, i.isLt]

/-- The actual quadratic radicands in the source variable `x`. -/
def radicand {b : ℕ} (a w : Fin b → ℝ) (i : ℕ) : Polynomial ℝ :=
  Polynomial.C ((extend a i)^2) + Polynomial.C ((extend w i)^2)*Polynomial.X^2

theorem radicand_degree {b : ℕ} (a w : Fin b → ℝ) (i : ℕ) :
    (radicand a w i).natDegree≤2 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by simp)

def rootValues {b : ℕ} (a w : Fin b → ℝ) (x : ℝ) (i : ℕ) : ℝ :=
  Real.sqrt ((extend a i)^2+(extend w i)^2*x^2)

theorem rootValues_sq {b : ℕ} (a w : Fin b → ℝ) (x : ℝ) (i : ℕ) :
    rootValues a w x i ^ 2=(radicand a w i).eval x := by
  simp only [rootValues, radicand, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

def branchPlus {b : ℕ} (c : Fin b → ℝ) (i : Fin b) : Tower b :=
  add b (embed b (Polynomial.C (c i))) (radical b i)

def branchMinus {b : ℕ} (c : Fin b → ℝ) (i : Fin b) : Tower b :=
  sub b (embed b (Polynomial.C (c i))) (radical b i)

theorem bounded_branchPlus {b : ℕ} (c : Fin b → ℝ) (i : Fin b) :
    Bounded b (branchPlus c i) 1 :=
  bounded_add (bounded_embed _ _ _ (Or.inr (by simp))) (bounded_radical b i)

theorem bounded_branchMinus {b : ℕ} (c : Fin b → ℝ) (i : Fin b) :
    Bounded b (branchMinus c i) 1 :=
  bounded_sub (bounded_embed _ _ _ (Or.inr (by simp))) (bounded_radical b i)

@[simp] theorem eval_branchPlus {b : ℕ} (c a w : Fin b → ℝ) (i : Fin b)
    (x : ℝ) (σ : Fin b → Bool) :
    eval b (branchPlus c i) x (rootValues a w x) σ =
      signedBranch (σ i) (c i) (a i) (w i) x := by
  simp [branchPlus, rootValues, signedBranch_eq_add_signedRoot]

@[simp] theorem eval_branchMinus {b : ℕ} (c a w : Fin b → ℝ) (i : Fin b)
    (x : ℝ) (σ : Fin b → Bool) :
    eval b (branchMinus c i) x (rootValues a w x) σ =
      signedBranch (!(σ i)) (c i) (a i) (w i) x := by
  simp [branchMinus, rootValues, signedBranch_not_eq_sub_signedRoot]

/-- The exact finite spectral product in the radical tower. -/
def spectralTower {b : ℕ} (c a w : Fin b → ℝ) (n k : Fin b → ℕ) : Tower b :=
  product (radicand a w) b b fun i => mul (radicand a w) b
    (power (radicand a w) b (branchPlus c i) (n i-k i))
    (power (radicand a w) b (branchMinus c i) (k i))

@[simp] theorem eval_spectralTower {b : ℕ} (c a w : Fin b → ℝ) (n k : Fin b → ℕ)
    (x : ℝ) (σ : Fin b → Bool) :
    eval b (spectralTower c a w n k) x (rootValues a w x) σ =
      spectralProduct Finset.univ c a w n k σ x := by
  simp only [spectralTower, eval_product _ _ _ _ _ _ (rootValues_sq a w x),
    eval_mul _ _ _ _ _ _ (rootValues_sq a w x),
    eval_power _ _ _ _ _ _ (rootValues_sq a w x), eval_branchPlus, eval_branchMinus,
    spectralProduct]

theorem bounded_spectralTower {b : ℕ} (c a w : Fin b → ℝ) (n k : Fin b → ℕ)
    (hk : ∀ i, k i≤n i) : Bounded b (spectralTower c a w n k) (∑ i, (n i : ℤ)) := by
  apply bounded_product _ (radicand_degree a w)
  intro i
  have h := bounded_mul _ (radicand_degree a w)
    (bounded_power _ (radicand_degree a w) (bounded_branchPlus c i) (n i-k i))
    (bounded_power _ (radicand_degree a w) (bounded_branchMinus c i) (k i))
  simpa only [mul_one, ← Nat.cast_add, Nat.sub_add_cancel (hk i)] using h

/-- Explicit polynomial eliminating all branch signs of a product difference. -/
def collisionPolynomial {b : ℕ} (c a w : Fin b → ℝ) (n k l : Fin b → ℕ) : Polynomial ℝ :=
  norm (radicand a w) b (sub b (spectralTower c a w n k) (spectralTower c a w n l))

theorem collisionPolynomial_degree {b : ℕ} (c a w : Fin b → ℝ) (n k l : Fin b → ℕ)
    (hk : ∀ i, k i≤n i) (hl : ∀ i, l i≤n i) :
    (collisionPolynomial c a w n k l).natDegree≤2^b*(∑ i, n i) := by
  have hh := bounded_norm _ (radicand_degree a w)
    (bounded_sub (bounded_spectralTower c a w n k hk) (bounded_spectralTower c a w n l hl))
  change collisionPolynomial c a w n k l=0 ∨
    ((collisionPolynomial c a w n k l).natDegree : ℤ)≤2^b*(∑ i, (n i : ℤ)) at hh
  rcases hh with hzero|hdegree
  · simp [hzero]
  · exact_mod_cast hdegree

/-- Its evaluation is nonzero precisely when every conjugate difference
is nonzero. This statement holds for every real `x`. -/
theorem collisionPolynomial_eval_ne_zero_iff {b : ℕ} (c a w : Fin b → ℝ)
    (n k l : Fin b → ℕ) (x : ℝ) :
    (collisionPolynomial c a w n k l).eval x≠0 ↔
      ∀ σ : Fin b → Bool,
        spectralProduct Finset.univ c a w n k σ x ≠ spectralProduct Finset.univ c a w n l σ x := by
  rw [collisionPolynomial, eval_norm_ne_zero_iff _ _ _ _ _ (rootValues_sq a w x)]
  simp only [eval_sub, eval_spectralTower, sub_ne_zero]

/-- A genuine spectral collision is a root of the explicit polynomial. -/
theorem collisionPolynomial_eval_eq_zero {b : ℕ} (c a w : Fin b → ℝ)
    (n k l : Fin b → ℕ) (x : ℝ) (σ : Fin b → Bool)
    (heq : spectralProduct Finset.univ c a w n k σ x =
      spectralProduct Finset.univ c a w n l σ x) :
    (collisionPolynomial c a w n k l).eval x=0 := by
  by_contra hn
  exact ((collisionPolynomial_eval_ne_zero_iff c a w n k l x).mp hn σ) heq

/-- The polynomial is genuinely nonzero when any unequal-diagonal class
has a differing smaller-branch count. -/
theorem collisionPolynomial_ne_zero {b : ℕ} (c a w : Fin b → ℝ) (n k l : Fin b → ℕ)
    (hc : ∀ i, 0<c i) (hca : ∀ i, c i^2-a i^2=1)
    (hw : ∀ i, 0<w i) (hw1 : ∀ i, w i<1)
    (hinj : Set.InjOn (fun i => (a i/w i)^2) {i | a i≠0})
    (hk : ∀ i, k i≤n i) (hl : ∀ i, l i≤n i)
    (hdiff : ∃ g, a g≠0 ∧ k g≠l g) : collisionPolynomial c a w n k l≠0 := by
  obtain ⟨x, _, hx⟩ := exists_all_conjugates_product_ne_zero c a w n k l
    hc hca hw hw1 hinj hk hl hdiff
  have hne : (collisionPolynomial c a w n k l).eval x≠0 := by
    apply (collisionPolynomial_eval_ne_zero_iff c a w n k l x).mpr
    intro σ
    exact sub_ne_zero.mp ((Finset.prod_ne_zero_iff.mp hx) σ (Finset.mem_univ σ))
  intro hz
  exact hne (by simp [hz])

/-- No finite collection of collisions can exceed the explicit degree
bound. There is no zero-count or nonvanishing oracle in the hypotheses. -/
theorem collision_card_le {b : ℕ} (c a w : Fin b → ℝ) (n k l : Fin b → ℕ)
    (hc : ∀ i, 0<c i) (hca : ∀ i, c i^2-a i^2=1)
    (hw : ∀ i, 0<w i) (hw1 : ∀ i, w i<1)
    (hinj : Set.InjOn (fun i => (a i/w i)^2) {i | a i≠0})
    (hk : ∀ i, k i≤n i) (hl : ∀ i, l i≤n i)
    (hdiff : ∃ g, a g≠0 ∧ k g≠l g) (T : Finset ℝ) (σ : Fin b → Bool)
    (hT : ∀ x∈T, spectralProduct Finset.univ c a w n k σ x =
      spectralProduct Finset.univ c a w n l σ x) : T.card≤2^b*(∑ i, n i) := by
  exact (PolynomialProductZeros.polynomial_zero_card_le _
    (collisionPolynomial_ne_zero c a w n k l hc hca hw hw1 hinj hk hl hdiff) T
    (fun x hx => collisionPolynomial_eval_eq_zero c a w n k l x σ (hT x hx))).trans
      (collisionPolynomial_degree c a w n k l hk hl)

end PlanarHom.BooleanExceptionalPolynomial
