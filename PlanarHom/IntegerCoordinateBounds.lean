import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Integer coordinate certificates for words in fixed number-field constants

Multiplication by each fixed alphabet value is a fixed rational coordinate
matrix. A single positive integer clears all those matrices and the coordinates
of one. Products of arbitrary length therefore have one controlled common
denominator and exponentially bounded integer coordinate numerators.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace PlanarHom.IntegerCoordinateBounds

/-- A single positive natural clears any finite family of rational denominators. -/
theorem exists_common_denominator {ι : Type*} [Fintype ι] (f : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ z : ι → ℤ, ∀ i, (D : ℚ) * f i = z i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) f
  have hbpos : (0 : ℤ) < b.val := b.property
  let D := b.val.toNat
  have hD : (D : ℤ) = b.val := Int.toNat_of_nonneg hbpos.le
  have hDpos : 0 < D := by
    have hbD : (0 : ℤ) < (D : ℤ) := hD.symm ▸ hbpos
    exact_mod_cast hbD
  have hi : ∀ i, ∃ z : ℤ, (D : ℚ) * f i = z := by
    intro i
    obtain ⟨z, hz⟩ := hb i
    refine ⟨z, ?_⟩
    have hDq : (D : ℚ) = (b.val : ℚ) := by exact_mod_cast hD
    rw [hDq]
    simpa [Algebra.smul_def] using hz.symm
  choose z hz using hi
  exact ⟨D, hDpos, z, hz⟩

/-- Absolute values of a finite integer sum obey the ordinary triangle bound. -/
theorem natAbs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

variable {K : Type*} [Field K] [Algebra ℚ K]
variable {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

/-- Rational matrix for multiplication by one fixed value. -/
def multiplicationMatrix (a : K) : Matrix (Fin dimension) (Fin dimension) ℚ :=
  LinearMap.toMatrix basis basis (LinearMap.mulRight ℚ a)

/-- The fixed multiplication matrix computes the actual basis coordinates. -/
theorem multiplicationMatrix_mulVec (a x : K) :
    multiplicationMatrix basis a *ᵥ basis.equivFun x = basis.equivFun (x * a) := by
  simpa only [multiplicationMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr basis basis (LinearMap.mulRight ℚ a) x

variable {ι : Type*} [Fintype ι]

/-- Integer matrices and an integer unit vector with one shared positive denominator. -/
structure ClearedCoordinates (A : ι → K) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  initial : Fin dimension → ℤ
  transition : ι → Matrix (Fin dimension) (Fin dimension) ℤ
  initial_spec : ∀ i, (denominator : ℚ) * basis.equivFun 1 i = initial i
  transition_spec : ∀ a i j,
    (denominator : ℚ) * multiplicationMatrix basis (A a) i j = transition a i j

/-- The integer coordinate data exist for every fixed finite alphabet. -/
theorem exists_clearedCoordinates (A : ι → K) : Nonempty (ClearedCoordinates basis A) := by
  let f : Fin dimension ⊕ (ι × Fin dimension × Fin dimension) → ℚ
    | .inl i => basis.equivFun 1 i
    | .inr p => multiplicationMatrix basis (A p.1) p.2.1 p.2.2
  obtain ⟨D, hD, z, hz⟩ := exists_common_denominator f
  exact ⟨⟨D, hD, fun i => z (.inl i), fun a i j => z (.inr (a, i, j)),
    fun i => hz (.inl i), fun a i j => hz (.inr (a, i, j))⟩⟩

/-- Explicit integer numerator recurrence for a word in the alphabet. -/
def numeratorWord {basis : Module.Basis (Fin dimension) ℚ K} {A : ι → K} (data : ClearedCoordinates basis A) :
    List ι → Fin dimension → ℤ
  | [] => data.initial
  | a :: xs => fun i => ∑ j, data.transition a i j * numeratorWord data xs j

omit [Fintype ι] in
/-- The numerator recurrence represents the actual field product exactly. -/
theorem coordinates_word {A : ι → K} (data : ClearedCoordinates basis A) (xs : List ι)
    (i : Fin dimension) :
    basis.equivFun ((xs.map A).prod) i =
      (numeratorWord data xs i : ℚ) / (data.denominator : ℚ) ^ (xs.length + 1) := by
  have hD : (data.denominator : ℚ) ≠ 0 := by exact_mod_cast data.denominator_pos.ne'
  induction xs generalizing i with
  | nil =>
    simp only [List.map_nil, List.prod_nil, numeratorWord, List.length_nil, Nat.zero_add, pow_one]
    apply (eq_div_iff hD).mpr
    simpa only [mul_comm] using data.initial_spec i
  | cons a xs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, numeratorWord]
    rw [mul_comm (A a) ((xs.map A).prod), ← multiplicationMatrix_mulVec basis (A a)]
    simp only [Matrix.mulVec, dotProduct]
    have hmat (j : Fin dimension) : multiplicationMatrix basis (A a) i j =
        (data.transition a i j : ℚ) / data.denominator := by
      apply (eq_div_iff hD).mpr
      simpa only [mul_comm] using data.transition_spec a i j
    simp_rw [hmat, ih]
    rw [Int.cast_sum]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [Int.cast_mul]
    field_simp
    ring

/-- Sum of the absolute integer transition coefficients, a fixed alphabet constant. -/
def transitionBound {basis : Module.Basis (Fin dimension) ℚ K} {A : ι → K}
    (data : ClearedCoordinates basis A) : ℕ :=
  ∑ a, ∑ i, ∑ j, (data.transition a i j).natAbs

/-- One fixed growth constant dominates the unit numerator and every matrix row bound. -/
def growthConstant {basis : Module.Basis (Fin dimension) ℚ K} {A : ι → K}
    (data : ClearedCoordinates basis A) : ℕ :=
  max 1 (max (∑ i, (data.initial i).natAbs) (dimension * transitionBound data))

theorem initial_le_growth {A : ι → K} (data : ClearedCoordinates basis A) (i : Fin dimension) :
    (data.initial i).natAbs ≤ growthConstant data := by
  apply (Finset.single_le_sum (fun j _ => Nat.zero_le (data.initial j).natAbs)
    (Finset.mem_univ i)).trans
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem transition_entry_le_bound {A : ι → K} (data : ClearedCoordinates basis A)
    (a : ι) (i j : Fin dimension) : (data.transition a i j).natAbs ≤ transitionBound data := by
  apply (Finset.single_le_sum (fun k _ => Nat.zero_le (data.transition a i k).natAbs)
    (Finset.mem_univ j)).trans
  apply (Finset.single_le_sum (fun k _ => Nat.zero_le (∑ l, (data.transition a k l).natAbs))
    (Finset.mem_univ i)).trans
  exact Finset.single_le_sum (fun b _ => Nat.zero_le (∑ k, ∑ l, (data.transition b k l).natAbs))
    (Finset.mem_univ a)

theorem dimension_mul_transitionBound_le_growth {A : ι → K} (data : ClearedCoordinates basis A) :
    dimension * transitionBound data ≤ growthConstant data :=
  (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

/-- Word-coordinate integer numerators grow at most exponentially in word length. -/
theorem numeratorWord_bound {A : ι → K} (data : ClearedCoordinates basis A)
    (xs : List ι) (i : Fin dimension) :
    (numeratorWord data xs i).natAbs ≤ growthConstant data ^ (xs.length + 1) := by
  induction xs generalizing i with
  | nil => simpa [numeratorWord] using initial_le_growth basis data i
  | cons a xs ih =>
    simp only [numeratorWord, List.length_cons]
    calc
      (∑ j, data.transition a i j * numeratorWord data xs j).natAbs ≤
          ∑ j, (data.transition a i j * numeratorWord data xs j).natAbs := natAbs_sum_le _ _
      _ ≤ ∑ j : Fin dimension, transitionBound data * growthConstant data ^ (xs.length + 1) := by
        apply Finset.sum_le_sum
        intro j _
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (transition_entry_le_bound basis data a i j) (ih j)
      _ = dimension * transitionBound data * growthConstant data ^ (xs.length + 1) := by
        simp [Nat.mul_assoc]
      _ ≤ growthConstant data * growthConstant data ^ (xs.length + 1) :=
        Nat.mul_le_mul_right _ (dimension_mul_transitionBound_le_growth basis data)
      _ = growthConstant data ^ (xs.length + 1 + 1) := (pow_succ' (growthConstant data) (xs.length + 1)).symm

omit [Fintype ι] in
/-- Sum of equal-length words retains a single common denominator. -/
theorem coordinates_sum_words {A : ι → K} (data : ClearedCoordinates basis A)
    {J : Type*} [Fintype J] (words : J → List ι) (L : ℕ)
    (hlen : ∀ j, (words j).length = L) (i : Fin dimension) :
    basis.equivFun (∑ j, ((words j).map A).prod) i =
      ((∑ j, numeratorWord data (words j) i : ℤ) : ℚ) / (data.denominator : ℚ) ^ (L + 1) := by
  simp only [map_sum, Finset.sum_apply]
  simp_rw [coordinates_word basis data, hlen]
  rw [Int.cast_sum, Finset.sum_div]

/-- The numerator of a sum has only the multiplicative assignment-count factor. -/
theorem sum_words_numerator_bound {A : ι → K} (data : ClearedCoordinates basis A)
    {J : Type*} [Fintype J] (words : J → List ι) (L : ℕ)
    (hlen : ∀ j, (words j).length = L) (i : Fin dimension) :
    (∑ j, numeratorWord data (words j) i).natAbs ≤
      Fintype.card J * growthConstant data ^ (L + 1) := by
  apply (natAbs_sum_le _ _).trans
  have h : ∀ j, (numeratorWord data (words j) i).natAbs ≤ growthConstant data ^ (L + 1) := by
    intro j
    simpa only [hlen j] using numeratorWord_bound basis data (words j) i
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)

end PlanarHom.IntegerCoordinateBounds
