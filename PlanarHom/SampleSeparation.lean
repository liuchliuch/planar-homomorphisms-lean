import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval.Finset.Nat

/-!
# A finite separating sample

The union bound gives a single sample distinguishing every inequivalent
pair in a finite family. If there are `N` indices and each inequivalent
pair agrees at at most `D` candidate samples, more than `N² * D` candidates
suffice. Equal functions (and repeated indices) are explicitly excluded
from the bad pairs.

This is the finite combinatorial step underlying Lemma 3.10, not the full
lemma or a claim about computational complexity. In particular, this file
does not establish a zero bound, effective equality testing, or bounds on
the bit lengths of sample values.
-/

namespace PlanarHom.SampleSeparation

variable {I A K : Type*} [Fintype I]

/-- A sample outside the union of all bad-pair sets detects exactly the
relation `R`. The only required property of `R` is that related indices
have the same values at every candidate sample; in applications it is
usually equality of the underlying functions. No nonemptiness assumption
on the index type, and no positivity assumption on `D`, is needed. -/
theorem exists_separating_sample_of_card [DecidableEq K]
    (value : I → A → K) (R : I → I → Prop) (S : Finset A) (D : ℕ)
    (hrespect : ∀ i j, R i j → ∀ a ∈ S, value i a = value j a)
    (hbad : ∀ i j, ¬ R i j →
      (S.filter fun a => value i a = value j a).card ≤ D)
    (hcard : Fintype.card I ^ 2 * D < S.card) :
    ∃ a ∈ S, ∀ i j, value i a = value j a ↔ R i j := by
  classical
  let bad : I × I → Finset A := fun p =>
    if R p.1 p.2 then ∅ else S.filter fun a => value p.1 a = value p.2 a
  have hbad_card (p : I × I) : (bad p).card ≤ D := by
    dsimp [bad]
    split_ifs with hp
    · simp
    · exact hbad p.1 p.2 hp
  have hunion : (Finset.univ.biUnion bad).card ≤ Fintype.card I ^ 2 * D := by
    simpa [Fintype.card_prod, pow_two] using
      Finset.card_biUnion_le_card_mul (Finset.univ : Finset (I × I)) bad D
        (fun p _ => hbad_card p)
  obtain ⟨a, ha, hgood⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (hunion.trans_lt hcard)
  refine ⟨a, ha, fun i j => ⟨?_, fun hij => hrespect i j hij a ha⟩⟩
  intro heq
  by_contra hij
  apply hgood
  apply Finset.mem_biUnion.mpr
  refine ⟨(i, j), Finset.mem_univ _, ?_⟩
  simp only [bad, hij, ↓reduceIte, Finset.mem_filter]
  exact ⟨ha, heq⟩

/-- With function equality as the relation, one finite sample separates
all distinct functions in the family. Duplicate functions are allowed. -/
theorem exists_function_separating_sample_of_card [DecidableEq K]
    (f : I → A → K) (S : Finset A) (D : ℕ)
    (hbad : ∀ i j, f i ≠ f j →
      (S.filter fun a => f i a = f j a).card ≤ D)
    (hcard : Fintype.card I ^ 2 * D < S.card) :
    ∃ a ∈ S, ∀ i j, f i a = f j a ↔ f i = f j := by
  apply exists_separating_sample_of_card f (fun i j => f i = f j) S D
    (fun i j hij a _ => congrFun hij a) hbad hcard

/-- Among the `N² * D + 1` consecutive natural-number samples starting
at `n₀`, one detects precisely `R`, provided each unrelated pair agrees
at at most `D` of those samples. The endpoints are included. -/
theorem exists_separating_nat_sample_in_Icc [DecidableEq K]
    (value : I → ℕ → K) (R : I → I → Prop) (n₀ D : ℕ)
    (hrespect : ∀ i j, R i j → ∀ n, value i n = value j n)
    (hbad : ∀ i j, ¬ R i j →
      ((Finset.Icc n₀ (n₀ + Fintype.card I ^ 2 * D)).filter
        fun n => value i n = value j n).card ≤ D) :
    ∃ n, n₀ ≤ n ∧ n ≤ n₀ + Fintype.card I ^ 2 * D ∧
      ∀ i j, value i n = value j n ↔ R i j := by
  obtain ⟨n, hn, hsep⟩ := exists_separating_sample_of_card value R
    (Finset.Icc n₀ (n₀ + Fintype.card I ^ 2 * D)) D
    (fun i j hij n _ => hrespect i j hij n) hbad (by
      rw [Nat.card_Icc]
      omega)
  exact ⟨n, (Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2, hsep⟩

/-- A finite zero-count hypothesis gives a bounded separating integer.
The functions may have any domain `A`, with their integer samples
specified by `sample`; the conclusion tests equality on all of `A`, not
merely equality on the sampled points. For real functions, take
`sample n = (n : ℝ)`.

The hypothesis says every finite collection of integer samples on which
a distinct pair agrees has cardinality at most `D`. It remains meaningful
without assuming the agreement set finite in advance. -/
theorem exists_function_separating_nat_sample
    (f : I → A → K) (sample : ℕ → A) (n₀ D : ℕ)
    (hbad : ∀ i j, f i ≠ f j → ∀ T : Finset ℕ,
      (∀ n ∈ T, f i (sample n) = f j (sample n)) → T.card ≤ D) :
    ∃ n, n₀ ≤ n ∧ n ≤ n₀ + Fintype.card I ^ 2 * D ∧
      ∀ i j, f i (sample n) = f j (sample n) ↔ f i = f j := by
  classical
  apply exists_separating_nat_sample_in_Icc (fun i n => f i (sample n))
    (fun i j => f i = f j) n₀ D
  · intro i j hij n
    exact congrFun hij (sample n)
  · intro i j hij
    apply hbad i j hij
    intro n hn
    exact (Finset.mem_filter.mp hn).2

/-- The direct natural-number version, using only the agreement bound on
the proposed interval. -/
theorem exists_function_separating_nat_in_Icc [DecidableEq K]
    (f : I → ℕ → K) (n₀ D : ℕ)
    (hbad : ∀ i j, f i ≠ f j →
      ((Finset.Icc n₀ (n₀ + Fintype.card I ^ 2 * D)).filter
        fun n => f i n = f j n).card ≤ D) :
    ∃ n, n₀ ≤ n ∧ n ≤ n₀ + Fintype.card I ^ 2 * D ∧
      ∀ i j, f i n = f j n ↔ f i = f j := by
  exact exists_separating_nat_sample_in_Icc f (fun i j => f i = f j) n₀ D
    (fun i j hij n => congrFun hij n) hbad

/-- An agreement bound on the original domain also bounds any injective
sequence of samples. This form can be combined directly with a bound on
the number of zeros of a difference of two real functions. -/
theorem exists_function_separating_nat_sample_of_injective
    (f : I → A → K) (sample : ℕ → A) (hsample : Function.Injective sample)
    (n₀ D : ℕ)
    (hbad : ∀ i j, f i ≠ f j → ∀ T : Finset A,
      (∀ a ∈ T, f i a = f j a) → T.card ≤ D) :
    ∃ n, n₀ ≤ n ∧ n ≤ n₀ + Fintype.card I ^ 2 * D ∧
      ∀ i j, f i (sample n) = f j (sample n) ↔ f i = f j := by
  classical
  apply exists_function_separating_nat_sample f sample n₀ D
  intro i j hij T hT
  have h := hbad i j hij (T.image sample) (by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    exact hT n hn)
  simpa only [Finset.card_image_of_injective T hsample] using h

end PlanarHom.SampleSeparation
