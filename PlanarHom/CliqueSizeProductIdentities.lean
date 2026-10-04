import PlanarHom.CliqueSizePolynomials

/-! NEW unique-factorization proof for size-selective clique product identities.
The source polynomials are the proved literal two-edge clique kernels. -/
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators Polynomial
namespace PlanarHom.CliqueSizePolynomials
open Polynomial

theorem multiplicity_diagonal {s k : ℕ} (hs : 2 ≤ s) (hk : 2 ≤ k) :
    emultiplicity (primeFactor s) (diagonal k) = if s=k then 1 else 0 := by
  have hc : (k:ℝ)-1 ≠ 0 := by exact_mod_cast (show (k:ℤ)-1 ≠ 0 by omega)
  rw [diagonal_eq_factor hk, emultiplicity_mul (factor_prime hs),
    emultiplicity_eq_zero.mpr (factor_not_dvd_constant _ hc), zero_add]
  by_cases h : s=k
  · subst k
    simp only [ite_true]
    simpa only [pow_one] using emultiplicity_pow_self (factor_prime hs).ne_zero
      (factor_prime hs).not_unit 1
  · rw [if_neg h]
    exact emultiplicity_eq_zero.mpr (fun hdiv => h ((factor_dvd_factor_iff s k).mp hdiv))

theorem multiplicity_offDiagonal {s : ℕ} (hs : 2 ≤ s) (k : ℕ) :
    emultiplicity (primeFactor s) (offDiagonal k) = 0 :=
  emultiplicity_eq_zero.mpr (factor_not_dvd_offDiagonal hs k)

def entry (k : ℕ) (same : Bool) : ℝ[X] := if same then diagonal k else offDiagonal k

theorem multiplicity_entry {s k : ℕ} (hs : 2 ≤ s) (hk : 2 ≤ k) (same : Bool) :
    emultiplicity (primeFactor s) (entry k same) =
      if k=s ∧ same=true then 1 else 0 := by
  cases same <;> simp [entry, multiplicity_diagonal hs hk, multiplicity_offDiagonal hs, eq_comm]

def selectedCount {I : Type*} [Fintype I] (s : ℕ) (size : I → ℕ) (same : I → Bool) : ℕ :=
  ∑ i, if size i=s ∧ same i=true then 1 else 0

theorem multiplicity_product {I : Type*} [Fintype I] {s : ℕ} (hs : 2 ≤ s)
    (size : I → ℕ) (hsize : ∀ i, 2 ≤ size i) (same : I → Bool) :
    emultiplicity (primeFactor s) (∏ i, entry (size i) (same i)) =
      (selectedCount s size same : ℕ∞) := by
  rw [Finset.emultiplicity_prod (factor_prime hs)]
  simp_rw [multiplicity_entry hs (hsize _)]
  simp [selectedCount, Nat.cast_sum, Nat.cast_ite]

/-- An identity of literal polynomial products preserves each size-specific
number of diagonal occurrences. The index sets need not have equal cardinality. -/
theorem selectedCount_eq_of_polynomial_products {I J : Type*} [Fintype I] [Fintype J]
    {s : ℕ} (hs : 2 ≤ s) (size : I → ℕ) (hsize : ∀ i, 2 ≤ size i)
    (same : I → Bool) (size' : J → ℕ) (hsize' : ∀ j, 2 ≤ size' j)
    (same' : J → Bool)
    (h : (∏ i, entry (size i) (same i)) = ∏ j, entry (size' j) (same' j)) :
    selectedCount s size same = selectedCount s size' same' := by
  have hm := congrArg (emultiplicity (primeFactor s)) h
  rw [multiplicity_product hs size hsize same,
    multiplicity_product hs size' hsize' same'] at hm
  exact_mod_cast hm

/-- The exact functional identity premise required by polynomial interpolation
has the same consequence, since real polynomial evaluation is injective. -/
theorem selectedCount_eq_of_function_products {I J : Type*} [Fintype I] [Fintype J]
    {s : ℕ} (hs : 2 ≤ s) (size : I → ℕ) (hsize : ∀ i, 2 ≤ size i)
    (same : I → Bool) (size' : J → ℕ) (hsize' : ∀ j, 2 ≤ size' j)
    (same' : J → Bool)
    (h : ∀ t : ℝ, (∏ i, (entry (size i) (same i)).eval t) =
      ∏ j, (entry (size' j) (same' j)).eval t) :
    selectedCount s size same = selectedCount s size' same' := by
  apply selectedCount_eq_of_polynomial_products hs size hsize same size' hsize' same'
  apply Polynomial.funext
  intro t
  simpa only [eval_prod] using h t

end PlanarHom.CliqueSizePolynomials
