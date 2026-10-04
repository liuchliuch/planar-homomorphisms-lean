import PlanarHom.Quotient
import PlanarHom.RootedColorRestriction
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Row facts for the actual twin quotient

Positive class weights remain positive. For a symmetric matrix, deletion of
zero rows also deletes only zero columns, so every retained row is nonzero and
distinct retained rows remain distinct. Applied to a zero–one actual quotient,
this gives nonproportional rows over every real scalar.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.Twins

variable {C K : Type*}

/-- Every actual-row class contains a representative, so aggregating strictly
positive weights gives a strictly positive class weight. -/
theorem quotientWeight_pos [Fintype C] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (A : Matrix C C K) (w : C → K)
    (hw : ∀ i, 0 < w i) (x : Quotient (rowSetoid A)) :
    0 < quotientWeight A w x := by
  induction x using Quotient.inductionOn with
  | h i =>
    unfold quotientWeight
    apply Finset.sum_pos
    · intro j _
      exact hw j.val
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨i, rfl⟩⟩

/-- The colors whose entire numerical row is not zero. -/
def nonzeroColor [Zero K] (M : Matrix C C K) : Set C := {i | M i ≠ 0}

/-- Every nonzero matrix has at least one nonzero row. No symmetry assumption
is needed for this fact. -/
theorem nonzeroColor_nonempty_of_ne_zero [Zero K] (M : Matrix C C K)
    (hM : M ≠ 0) : Nonempty (nonzeroColor M) := by
  by_contra h
  apply hM
  funext i
  apply not_not.mp
  intro hi
  exact h ⟨⟨i, hi⟩⟩

/-- A nonzero entry remains nonzero in the actual-row quotient. -/
theorem quotientMatrix_ne_zero_of_ne_zero [Zero K] (A : Matrix C C K)
    (hs : ∀ i j, A i j = A j i) (hA : A ≠ 0) : quotientMatrix A hs ≠ 0 := by
  intro h
  apply hA
  funext i j
  exact congrFun (congrFun h (Quotient.mk (rowSetoid A) i))
    (Quotient.mk (rowSetoid A) j)

/-- A nonzero symmetric source retains at least one actual-row class after
the zero row of its quotient is deleted. -/
theorem deletedQuotient_nonempty_of_ne_zero [Zero K] (A : Matrix C C K)
    (hs : ∀ i j, A i j = A j i) (hA : A ≠ 0) :
    Nonempty (nonzeroColor (quotientMatrix A hs)) :=
  nonzeroColor_nonempty_of_ne_zero _ (quotientMatrix_ne_zero_of_ne_zero A hs hA)

/-- Simultaneous restriction to the nonzero rows and their corresponding
columns. -/
def nonzeroMatrix [Zero K] (M : Matrix C C K) :
    Matrix (nonzeroColor M) (nonzeroColor M) K :=
  fun i j => M i.val j.val

@[simp] theorem nonzeroMatrix_apply [Zero K] (M : Matrix C C K)
    (i j : nonzeroColor M) : nonzeroMatrix M i j = M i.val j.val := rfl

/-- For a symmetric matrix every deleted column is identically zero. -/
theorem entry_eq_zero_of_not_nonzeroColor [Zero K] (M : Matrix C C K)
    (hs : ∀ i j, M i j = M j i) {j : C} (hj : j ∉ nonzeroColor M) (i : C) :
    M i j = 0 := by
  have hz : M j = 0 := not_not.mp hj
  exact (hs i j).trans (congrFun hz i)

theorem nonzeroMatrix_symmetric [Zero K] (M : Matrix C C K)
    (hs : ∀ i j, M i j = M j i) :
    ∀ i j, nonzeroMatrix M i j = nonzeroMatrix M j i :=
  fun i j => hs i.val j.val

/-- A nonzero row of a symmetric matrix remains nonzero after zero columns
are deleted. -/
theorem nonzeroMatrix_rows_ne_zero [Zero K] (M : Matrix C C K)
    (hs : ∀ i j, M i j = M j i) (i : nonzeroColor M) :
    nonzeroMatrix M i ≠ 0 := by
  intro h
  apply i.property
  funext j
  by_cases hj : j ∈ nonzeroColor M
  · exact congrFun h ⟨j, hj⟩
  · exact entry_eq_zero_of_not_nonzeroColor M hs hj i.val

/-- Deleting zero columns cannot identify two previously distinct rows. -/
theorem nonzeroMatrix_rows_injective [Zero K] (M : Matrix C C K)
    (hs : ∀ i j, M i j = M j i) (hrows : Function.Injective M) :
    Function.Injective (nonzeroMatrix M) := by
  intro i j h
  apply Subtype.ext
  apply hrows
  funext k
  by_cases hk : k ∈ nonzeroColor M
  · exact congrFun h ⟨k, hk⟩
  · exact (entry_eq_zero_of_not_nonzeroColor M hs hk i.val).trans
      (entry_eq_zero_of_not_nonzeroColor M hs hk j.val).symm

/-- Nonzero rows form a closed color set for rooted restriction. -/
theorem nonzeroColor_colorClosed {C K : Type} [Fintype C] [Field K]
    (M : Matrix C C K) (hs : ∀ i j, M i j = M j i) :
    RootedRestriction.ColorClosed M (nonzeroColor M) := by
  intro i _ j hij
  by_contra hj
  exact hij (entry_eq_zero_of_not_nonzeroColor M hs hj i)

/-- A proportionality between zero–one rows with a nonzero left row has
coefficient one, with no sign or nonzero assumption on the real scalar. -/
theorem zeroOne_proportional_eq_one (M : Matrix C C ℝ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) {i j : C} (hi : M i ≠ 0)
    (c : ℝ) (h : M i = c • M j) : c = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, M i k ≠ 0 := by
    by_contra hn
    apply hi
    funext k
    exact not_not.mp (not_exists.mp hn k)
  have hik : M i k = 1 := (h01 i k).resolve_left hk
  have he : (1 : ℝ) = c * M j k := by
    simpa only [hik, Pi.smul_apply, smul_eq_mul] using congrFun h k
  rcases h01 j k with hjk | hjk
  · simp only [hjk, mul_zero] at he
    exact (one_ne_zero he).elim
  · simpa only [hjk, mul_one] using he.symm

/-- Distinct nonzero zero–one rows are nonproportional over all real scalars. -/
theorem zeroOne_rows_nonproportional (M : Matrix C C ℝ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hnz : ∀ i, M i ≠ 0) (hrows : Function.Injective M)
    (i j : C) (hij : i ≠ j) (c : ℝ) : M i ≠ c • M j := by
  intro h
  have hc := zeroOne_proportional_eq_one M h01 (hnz i) c h
  rw [hc, one_smul] at h
  exact hij (hrows h)

/-- Taking the actual-row quotient preserves zero–one entries. -/
theorem quotientMatrix_zeroOne [Zero K] [One K] (A : Matrix C C K)
    (hs : ∀ i j, A i j = A j i) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    ∀ x y, quotientMatrix A hs x y = 0 ∨ quotientMatrix A hs x y = 1 := by
  intro x y
  induction x using Quotient.inductionOn with
  | h i =>
    induction y using Quotient.inductionOn with
    | h j => exact h01 i j

/-- The matrix obtained by deleting zero rows of the canonical actual-row
quotient of a symmetric zero–one matrix has no proportional distinct rows. -/
theorem deletedQuotient_rows_nonproportional (A : Matrix C C ℝ)
    (hs : ∀ i j, A i j = A j i) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (i j : nonzeroColor (quotientMatrix A hs)) (hij : i ≠ j) (c : ℝ) :
    nonzeroMatrix (quotientMatrix A hs) i ≠ c • nonzeroMatrix (quotientMatrix A hs) j := by
  apply zeroOne_rows_nonproportional _
    (fun x y => quotientMatrix_zeroOne A hs h01 x.val y.val)
    (nonzeroMatrix_rows_ne_zero _ (quotientMatrix_symmetric A hs))
    (nonzeroMatrix_rows_injective _ (quotientMatrix_symmetric A hs)
      (quotientMatrix_rows_injective A hs)) i j hij c

end PlanarHom.Twins
