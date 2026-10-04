import PlanarHom.BooleanFieldCollisionMachines
import PlanarHom.BooleanExceptionalSource

/-! The explicit grid contains enough samples accepted by the computable
base-field norm test itself, which is stronger than testing only the original
real branch collisions. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanFieldNormSamples
open BooleanExceptionalGrid BooleanExceptionalSampling BooleanExceptionalPolynomial
open BooleanFieldCollision
variable {K : Type} [Field K] [Algebra ℚ K]
variable {I : Type*} [Fintype I] {b : ℕ}

/-- The exact norm acceptance property for the finite index family. -/
def NormSeparates (f : K →+* ℝ) (c a w : Fin b → K) (n : Fin b → ℕ)
    (k : I → Fin b → ℕ) (q : ℚ) : Prop :=
  ∀ i j, (∃ g, f (a g)≠0 ∧ k i g≠k j g) →
    collision c a w (algebraMap ℚ K q) n (k i) (k j)≠0

def goodSamples (f : K →+* ℝ) (c a w : Fin b → K) (n : Fin b → ℕ)
    (k : I → Fin b → ℕ) (L : ℕ) : Finset ℚ := by
  classical
  exact (rationalGrid (exceptionalBound I n+L)).filter (NormSeparates f c a w n k)

@[simp] theorem mem_goodSamples (f : K →+* ℝ) (c a w : Fin b → K) (n : Fin b → ℕ)
    (k : I → Fin b → ℕ) (L : ℕ) (q : ℚ) :
    q∈goodSamples f c a w n k L ↔
      q∈rationalGrid (exceptionalBound I n+L) ∧ NormSeparates f c a w n k q := by
  classical
  simp [goodSamples]

/-- The finite norm-zero union bound on any rational candidate set. -/
theorem good_on_card_bound (f : K →+* ℝ) (c a w : Fin b → K)
    (n : Fin b → ℕ) (k : I → Fin b → ℕ) (S : Finset ℚ)
    (hp : BooleanExceptionalSource.SeparatedParameters
      (fun g => f (c g)) (fun g => f (a g)) (fun g => f (w g)))
    (hk : ∀ i g, k i g≤n g) :
    S.card≤(S.filter (NormSeparates f c a w n k)).card+exceptionalBound I n := by
  classical
  let pairs := forbiddenPairs (fun g => f (a g)) k
  let coll := fun p : I×I => fun q : ℚ =>
    collision c a w (algebraMap ℚ K q) n (k p.1) (k p.2)=0
  let P := fun p : I×I => collisionPolynomial
    (fun g => f (c g)) (fun g => f (a g)) (fun g => f (w g)) n (k p.1) (k p.2)
  have hP : ∀ p∈pairs, P p≠0 := by
    intro p hmem
    exact collisionPolynomial_ne_zero _ _ _ _ _ _ hp.c_pos hp.parameter_eq hp.w_pos
      hp.w_lt_one hp.branch_inj (hk p.1) (hk p.2) (mem_forbiddenPairs.mp hmem)
  have hdegree : ∀ p∈pairs, (P p).natDegree≤degreeBound n :=
    fun p _ => collisionPolynomial_degree _ _ _ _ _ _ (hk p.1) (hk p.2)
  have hzero : ∀ p∈pairs, ∀ q∈S,
      coll p q → (P p).eval (q : ℝ)=0 := by
    intro p _ q _ hz
    have he := collision_eval f c a w (algebraMap ℚ K q) n (k p.1) (k p.2)
    have hh : f (algebraMap ℚ K q)=(q : ℝ) := by simp
    rw [hh] at he
    exact he.symm.trans (by rw [show collision c a w (algebraMap ℚ K q) n (k p.1) (k p.2)=0 from hz,f.map_zero])
  have h := card_le_goodSamples_add pairs coll P (degreeBound n) S hP hdegree hzero
  have heq : BooleanExceptionalGrid.goodSamples pairs coll S = S.filter (NormSeparates f c a w n k) := by
    ext q
    simp only [BooleanExceptionalGrid.mem_goodSamples,Finset.mem_filter]
    constructor
    · rintro ⟨hq,h⟩
      refine ⟨hq,?_⟩
      intro i j hij
      exact h (i,j) (mem_forbiddenPairs.mpr hij)
    · rintro ⟨hq,h⟩
      refine ⟨hq,?_⟩
      intro p hp
      exact h p.1 p.2 (mem_forbiddenPairs.mp hp)
  rw [heq] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (card_forbiddenPairs_le _ k)) _)


/-- The actual norm test succeeds at at least L samples for every explicit
upper bound on the exceptional-set cardinality. -/
theorem normGrid_card_ge_of_bound (f : K →+* ℝ) (c a w : Fin b → K)
    (n : Fin b → ℕ) (k : I → Fin b → ℕ) (B L : ℕ)
    (hB : exceptionalBound I n≤B)
    (hp : BooleanExceptionalSource.SeparatedParameters
      (fun g => f (c g)) (fun g => f (a g)) (fun g => f (w g)))
    (hk : ∀ i g, k i g≤n g) :
    L≤((rationalGrid (B+L)).filter (NormSeparates f c a w n k)).card := by
  have h := good_on_card_bound f c a w n k (rationalGrid (B+L)) hp hk
  rw [card_rationalGrid] at h
  omega

/-- The exact bound from the frozen sample theorem also controls the
stronger, computable norm acceptance test. -/
theorem goodSamples_card_ge (f : K →+* ℝ) (c a w : Fin b → K)
    (n : Fin b → ℕ) (k : I → Fin b → ℕ) (L : ℕ)
    (hp : BooleanExceptionalSource.SeparatedParameters
      (fun g => f (c g)) (fun g => f (a g)) (fun g => f (w g)))
    (hk : ∀ i g, k i g≤n g) :
    L≤(goodSamples f c a w n k L).card :=
  normGrid_card_ge_of_bound f c a w n k (exceptionalBound I n) L le_rfl hp hk

omit [Fintype I] in
/-- Passing the field norm test guarantees the required real spectral
separation at the very same rational sample. -/
theorem NormSeparates.separates {f : K →+* ℝ} {c a w : Fin b → K} {n : Fin b → ℕ}
    {k : I → Fin b → ℕ} {q : ℚ} (h : NormSeparates f c a w n k q) :
    SeparatesUnequalCounts (fun g => f (c g)) (fun g => f (a g)) (fun g => f (w g)) n k (q : ℝ) := by
  intro i j heq g hag
  by_contra hkg
  have hn := h i j ⟨g,hag,hkg⟩
  have hz := collisionPolynomial_eval_eq_zero (fun g => f (c g)) (fun g => f (a g))
    (fun g => f (w g)) n (k i) (k j) (q : ℝ) (fun _ => false) heq
  have he := collision_eval f c a w (algebraMap ℚ K q) n (k i) (k j)
  have hq : f (algebraMap ℚ K q)=(q : ℝ) := by simp
  rw [hq,hz] at he
  exact hn (f.injective (he.trans f.map_zero.symm))

end PlanarHom.BooleanFieldNormSamples
