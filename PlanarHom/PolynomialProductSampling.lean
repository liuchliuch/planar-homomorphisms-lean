import PlanarHom.PolynomialProductZeros
import PlanarHom.FixedLengthProductRecovery

/-! Concrete polynomial source families provide a sample compatible at exactly
one marked occurrence count, with the source (3.7) polynomial sample bound. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.PolynomialProductZeros
open ExponentProductSemantics ExponentProductTables

private theorem sum_getD (xs : List ℕ) (t : ℕ) (hlen : xs.length = t) :
    (∑ i : Fin t, xs.getD i.val 0) = xs.sum := by
  subst t
  have h : List.ofFn (fun i : Fin xs.length => xs.getD i.val 0) = xs := by
    simpa only [List.getD_eq_getElem _ _ (Fin.isLt _)] using List.ofFn_getElem xs
  rw [← List.sum_ofFn, h]

/-- The fixed sample may depend on m. No compatibility for other product lengths
is required, and target entries may be zero or negative. -/
theorem exists_compatible_sample {t : ℕ} (F : Fin t → Polynomial ℝ) (B : Fin t → ℝ)
    (d m n₀ : ℕ) (hF : ∀ e, (F e).natDegree ≤ d)
    (hidentity : ∀ xs ∈ ExponentVectors.weak t m, ∀ ys ∈ ExponentVectors.weak t m,
      (fun x : ℝ => value (fun e => (F e).eval x) xs) =
        (fun x : ℝ => value (fun e => (F e).eval x) ys) → value B xs = value B ys) :
    ∃ n, n₀ ≤ n ∧ n ≤ n₀ + ((m + 1) ^ t) ^ 2 * (d * m) ∧
      CompatibleAt (fun e => (F e).eval (n : ℝ)) B m := by
  let W := ExponentVectors.weak t m
  let a : Fin W.length → Fin t → ℕ := fun i e => (W.get i).getD e.val 0
  have ha (i : Fin W.length) : ∑ e, a i e = m := by
    obtain ⟨hl, hs⟩ := (ExponentVectors.mem_weak t m (W.get i)).mp (List.get_mem W i)
    exact (sum_getD _ _ hl).trans hs
  obtain ⟨n, hn, hbound, hsep⟩ := exists_separating_integer F a d m n₀ hF ha
  refine ⟨n, hn, hbound.trans ?_, ?_⟩
  · simp only [Fintype.card_fin]
    have hw := ExponentVectors.length_weak_le t m
    change W.length ≤ (m + 1) ^ t at hw
    gcongr
  · intro xs hxs ys hys _ he
    apply hidentity xs hxs ys hys
    obtain ⟨i, hi⟩ := List.get_of_mem hxs
    obtain ⟨j, hj⟩ := List.get_of_mem hys
    have hs := (hsep i j).mp (by simpa only [a, W, hi, hj, value] using he)
    simpa only [a, W, hi, hj, value] using hs

/-- Eventual positivity is used only at the selected integer, with its original
fixed threshold. It gives a positive source alphabet for the dynamic recovery. -/
theorem exists_positive_compatible_sample {t : ℕ}
    (F : Fin t → Polynomial ℝ) (B : Fin t → ℝ) (d m n₀ : ℕ)
    (hF : ∀ e, (F e).natDegree ≤ d)
    (hpositive : ∀ n ≥ n₀, ∀ e, 0 < (F e).eval (n : ℝ))
    (hidentity : ∀ xs ∈ ExponentVectors.weak t m, ∀ ys ∈ ExponentVectors.weak t m,
      (fun x : ℝ => value (fun e => (F e).eval x) xs) =
        (fun x : ℝ => value (fun e => (F e).eval x) ys) → value B xs = value B ys) :
    ∃ n, n₀ ≤ n ∧ n ≤ n₀ + ((m + 1) ^ t) ^ 2 * (d * m) ∧
      (∀ e, 0 < (F e).eval (n : ℝ)) ∧
      CompatibleAt (fun e => (F e).eval (n : ℝ)) B m := by
  obtain ⟨n, hn, hb, hc⟩ := exists_compatible_sample F B d m n₀ hF hidentity
  exact ⟨n, hn, hb, hpositive n hn, hc⟩

end PlanarHom.PolynomialProductZeros
