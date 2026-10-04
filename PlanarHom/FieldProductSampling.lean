import PlanarHom.PolynomialProductSampling
import PlanarHom.SpectralProductSampling

/-! Exact sampling compatibility descends through the prescribed real field
embedding. This is value transport, not a claim of identical output codewords. -/
noncomputable section
namespace PlanarHom.FieldProductSampling
open ExponentProductSemantics ExponentProductTables
variable {K : Type} [Field K] {t : ℕ}

@[simp] theorem map_value (φ : K →+* ℝ) (A : Fin t → K) (xs : List ℕ) :
    φ (value A xs) = value (fun i => φ (A i)) xs := by
  simp [value, map_prod, map_pow]

theorem compatibleAt_iff_map (φ : K →+* ℝ) (A B : Fin t → K) (m : ℕ) :
    CompatibleAt A B m ↔ CompatibleAt (fun i => φ (A i)) (fun i => φ (B i)) m := by
  constructor
  · intro h xs hxs ys hys hz he
    rw [← map_value, ← map_value] at he
    rw [← map_value] at hz
    rw [← map_value, ← map_value]
    exact congrArg φ (h xs hxs ys hys (fun he => hz (by rw [he, map_zero])) (φ.injective he))
  · intro h xs hxs ys hys hz he
    apply φ.injective
    rw [map_value, map_value]
    apply h xs hxs ys hys
    · rw [← map_value]
      exact fun hzero => hz (φ.injective (hzero.trans (map_zero φ).symm))
    · rw [← map_value, ← map_value, he]

/-- Case(P)'s real separating argument returns exact compatibility in the
original fixed number field, with no ordering operation on encoded elements. -/
theorem polynomial_exists_compatible_sample (φ : K →+* ℝ)
    (F : Fin t → Polynomial K) (B : Fin t → K) (d m n₀ : ℕ)
    (hF : ∀ i, (F i).natDegree ≤ d)
    (hidentity : ∀ xs ∈ ExponentVectors.weak t m, ∀ ys ∈ ExponentVectors.weak t m,
      (fun x : ℝ => value (fun i => ((F i).map φ).eval x) xs) =
        (fun x : ℝ => value (fun i => ((F i).map φ).eval x) ys) → value B xs = value B ys) :
    ∃ n, n₀ ≤ n ∧ n ≤ n₀ + ((m + 1) ^ t) ^ 2 * (d * m) ∧
      CompatibleAt (fun i => (F i).eval (n : K)) B m := by
  obtain ⟨n, hn, hb, hc⟩ := PolynomialProductZeros.exists_compatible_sample
    (fun i => (F i).map φ) (fun i => φ (B i)) d m n₀
    (fun i => Polynomial.natDegree_map_le.trans (hF i)) (by
      intro xs hxs ys hys he
      rw [← map_value, ← map_value]
      exact congrArg φ (hidentity xs hxs ys hys he))
  refine ⟨n, hn, hb, (compatibleAt_iff_map φ _ _ m).mpr ?_⟩
  convert hc using 1
  funext i
  rw [Polynomial.eval_map]
  simp

end PlanarHom.FieldProductSampling
