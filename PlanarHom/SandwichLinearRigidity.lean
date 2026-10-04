import PlanarHom.SandwichDistanceLeading
import PlanarHom.SymmetricBCHSector

/-!
# Rational sandwich-log equalities determine the original matrix entries

The actual linear expansions on two rational sector rays identify both original
coefficients. This is the first-order extraction used to transfer opposite-edge
equalities to the logarithms in Proposition 4.8.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.SymmetricBCH
open MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Equality of actual log entries on a small rational ray identifies their
linear coefficients, with no differentiability premise left to discharge. -/
theorem linear_entries_eq_of_rational_sandwich_log_eq
    (C B : Matrix V V ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (η : ℝ) (i j k l : V)
    (hrational : ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε →
      EntropyCompletion.matrixLog (sandwich C (η • B) (q : ℝ)) i j =
      EntropyCompletion.matrixLog (sandwich C (η • B) (q : ℝ)) k l) :
    C i j + η * B i j = C k l + η * B k l := by
  have hηB : (η • B).IsHermitian := by
    change star (η • B) = η • B
    rw [star_smul, star_trivial]
    exact congrArg (fun A : Matrix V V ℝ => η • A) hB
  let f : ℝ → ℝ := fun t =>
    EntropyCompletion.matrixLog (sandwich C (η • B) t) i j -
    EntropyCompletion.matrixLog (sandwich C (η • B) t) k l
  have hf₁ := matrixLog_sandwich_entry_sub_linear_isBigO C (η • B) hC hηB i j
  have hf₂ := matrixLog_sandwich_entry_sub_linear_isBigO C (η • B) hC hηB k l
  have hf : (fun t => f t - ((C i j + η * B i j) - (C k l + η * B k l)) * t ^ 1)
      =O[𝓝 0] (fun t : ℝ => t ^ (1 + 1)) := by
    convert hf₁.sub hf₂ using 1
    funext t
    simp only [f, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, pow_one]
    ring
  have hfzero : f 0 = 0 := by
    have hlog : EntropyCompletion.matrixLog (1 : Matrix V V ℝ) = 0 := CFC.log_one
    simp [f, sandwich_zero, hlog]
  have hrat : ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε → f q = 0 := by
    obtain ⟨ε, hε, hr⟩ := hrational
    exact ⟨ε, hε, fun q hq hqε => sub_eq_zero.mpr (hr q hq hqε)⟩
  exact sub_eq_zero.mp
    (leading_coefficient_zero_of_rational_zeros f _ 1 hfzero hf hrat)

/-- Two distinct real slope parameters recover both original entries from
rational-time equality of the actual logarithmic sandwich entries. -/
theorem entries_eq_of_two_rational_sandwich_log_rays
    (C B : Matrix V V ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (η₁ η₂ : ℝ) (hne : η₁ ≠ η₂) (i j k l : V)
    (h₁ : ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε →
      EntropyCompletion.matrixLog (sandwich C (η₁ • B) (q : ℝ)) i j =
      EntropyCompletion.matrixLog (sandwich C (η₁ • B) (q : ℝ)) k l)
    (h₂ : ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε →
      EntropyCompletion.matrixLog (sandwich C (η₂ • B) (q : ℝ)) i j =
      EntropyCompletion.matrixLog (sandwich C (η₂ • B) (q : ℝ)) k l) :
    C i j = C k l ∧ B i j = B k l := by
  have he₁ := linear_entries_eq_of_rational_sandwich_log_eq C B hC hB η₁ i j k l h₁
  have he₂ := linear_entries_eq_of_rational_sandwich_log_eq C B hC hB η₂ i j k l h₂
  have hprod : (η₁ - η₂) * (B i j - B k l) = 0 := by nlinarith
  have hB' := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne))
  exact ⟨by rw [hB'] at he₁; linarith, hB'⟩

/-- An interval of positive rational slopes supplies the two required rays. -/
theorem entries_eq_of_rational_sandwich_log_sector
    (C B : Matrix V V ℝ) (hC : C.IsHermitian) (hB : B.IsHermitian)
    (δ : ℝ) (hδ : 0 < δ) (i j k l : V)
    (hsector : ∀ η : ℚ, 0 < (η : ℝ) → (η : ℝ) < δ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε →
        EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) (q : ℝ)) i j =
        EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) (q : ℝ)) k l) :
    C i j = C k l ∧ B i j = B k l := by
  obtain ⟨η, hηpos, hηlt⟩ := exists_rat_btwn (show (0 : ℝ) < δ / 2 by linarith)
  have hη : (η : ℝ) < δ := by linarith
  have htwoηpos : 0 < ((2 * η : ℚ) : ℝ) := by push_cast; positivity
  have htwoηlt : ((2 * η : ℚ) : ℝ) < δ := by push_cast; linarith
  apply entries_eq_of_two_rational_sandwich_log_rays C B hC hB (η : ℝ)
    ((2 * η : ℚ) : ℝ) _ i j k l (hsector η hηpos hη) (hsector (2 * η) htwoηpos htwoηlt)
  push_cast
  intro heq
  linarith

end PlanarHom.SymmetricBCH
