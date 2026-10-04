import PlanarHom.SampleSeparation
import PlanarHom.FixedLengthProductRecovery
import Mathlib.Data.Real.Basic

/-! Fixed-length source-product identities determine a bounded separating sample.
The zero bound is an explicit mathematical input here; polynomial and spectral
families discharge it in separate concrete modules. -/
noncomputable section
namespace PlanarHom.ProductFamilySampling
open ExponentProductSemantics ExponentProductTables
variable {t : ℕ}

def AgreementBound (F : ℝ → Fin t → ℝ) (m D : ℕ) : Prop :=
  ∀ xs ∈ ExponentVectors.weak t m, ∀ ys ∈ ExponentVectors.weak t m,
    (fun x => value (F x) xs) ≠ (fun x => value (F x) ys) →
    ∀ T : Finset ℝ, (∀ x ∈ T, value (F x) xs = value (F x) ys) → T.card ≤ D

/-- The exact source equivalence relation is determined by D+1 consecutive samples. -/
theorem identity_iff_consecutive (F : ℝ → Fin t → ℝ) (m D n₀ : ℕ)
    (hbound : AgreementBound F m D) (xs ys : List ℕ)
    (hxs : xs ∈ ExponentVectors.weak t m) (hys : ys ∈ ExponentVectors.weak t m) :
    (fun x => value (F x) xs) = (fun x => value (F x) ys) ↔
      ∀ j ≤ D, value (F ((n₀ + j : ℕ) : ℝ)) xs = value (F ((n₀ + j : ℕ) : ℝ)) ys := by
  constructor
  · intro h j _
    exact congrFun h _
  · intro h
    by_contra hne
    let T := (Finset.range (D + 1)).image fun j => ((n₀ + j : ℕ) : ℝ)
    have hc : T.card = D + 1 := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro x y hxy
        exact Nat.add_left_cancel (Nat.cast_injective hxy)
    have hh := hbound xs hxs ys hys hne T (by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact h j (by have := Finset.mem_range.mp hj; omega))
    omega

/-- The source parameter depends only on the current product length and target.
No all-length numerical compatibility premise is introduced. -/
theorem exists_compatible_sample (F : ℝ → Fin t → ℝ) (B : Fin t → ℝ)
    (m D n₀ : ℕ) (hbound : AgreementBound F m D)
    (hidentity : ∀ xs ∈ ExponentVectors.weak t m, ∀ ys ∈ ExponentVectors.weak t m,
      (fun x => value (F x) xs) = (fun x => value (F x) ys) → value B xs = value B ys) :
    ∃ n, n₀ ≤ n ∧ n ≤ n₀ + ((m + 1) ^ t) ^ 2 * D ∧ CompatibleAt (F n) B m := by
  let W := ExponentVectors.weak t m
  let f : Fin W.length → ℝ → ℝ := fun i x => value (F x) (W.get i)
  obtain ⟨n, hn, hb, hs⟩ := SampleSeparation.exists_function_separating_nat_sample_of_injective
    f (fun n => (n : ℝ)) Nat.cast_injective n₀ D (by
      intro i j hne T hT
      exact hbound (W.get i) (List.get_mem _ _) (W.get j) (List.get_mem _ _) hne T hT)
  refine ⟨n, hn, hb.trans ?_, ?_⟩
  · simp only [Fintype.card_fin]
    have hw := ExponentVectors.length_weak_le t m
    change W.length ≤ (m + 1) ^ t at hw
    gcongr
  · intro xs hxs ys hys _ he
    apply hidentity xs hxs ys hys
    obtain ⟨i, hi⟩ := List.get_of_mem hxs
    obtain ⟨j, hj⟩ := List.get_of_mem hys
    exact (by simpa only [f, W, hi, hj] using
      (hs i j).mp (by simpa only [f, W, hi, hj] using he))

end PlanarHom.ProductFamilySampling
