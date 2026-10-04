import PlanarHom.MatrixPowerLogExponential
import PlanarHom.MatrixExponentialRelations
import PlanarHom.EffectivePolynomialTransfer

/-!
# Full logarithmic support preserves Potts products

The analytic ingredient of source Lemma 3.11 uses nonzero, possibly negative,
off-diagonal logarithmic entries. Its finite product coefficient is nonzero;
no positivity assumption on the logarithm is used.
-/
noncomputable section
open scoped BigOperators Topology Matrix.Norms.Operator
open Filter Asymptotics
namespace PlanarHom.FullLogarithmicProductIdentities
open MatrixLogCoefficients EffectiveProductTransfer SymmetricProductIdentities
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The target is the Potts matrix with diagonal 2 and off-diagonal 1. -/
def pottsMatrix {K : Type*} [Semiring K] : Matrix V V K :=
  fun i j => if i = j then 2 else 1

theorem pottsMatrix_eq_one_add_ones {K : Type*} [Semiring K] :
    (pottsMatrix : Matrix V V K) = 1 + Matrix.of (fun _ _ => 1) := by
  ext i j
  by_cases hij : i = j <;> simp [pottsMatrix, hij, one_add_one_eq_two]

theorem pottsMatrix_symm {K : Type*} [Semiring K] (i j : V) :
    (pottsMatrix : Matrix V V K) i j = pottsMatrix j i := by
  simp only [pottsMatrix, eq_comm]

/-- Each diagonal position has order zero and each off-diagonal position order one. -/
def entryOrder (i j : V) : ℕ := if i = j then 0 else 1

def entryCoefficient (L : Matrix V V ℝ) (i j : V) : ℝ := if i = j then 1 else L i j

theorem entryCoefficient_ne_zero (L : Matrix V V ℝ)
    (hfull : ∀ i j, i ≠ j → L i j ≠ 0) (i j : V) : entryCoefficient L i j ≠ 0 := by
  by_cases hij : i = j
  · simp [entryCoefficient, hij]
  · simpa [entryCoefficient, hij] using hfull i j hij

/-- The actual exponential has the stated order and signed leading coefficient. -/
theorem exp_entry_leading_isBigO (L : Matrix V V ℝ) (i j : V) :
    (fun t => NormedSpace.exp ℝ (t • L) i j - entryCoefficient L i j * t ^ entryOrder i j)
      =O[𝓝 0] (fun t : ℝ => t ^ (entryOrder i j + 1)) := by
  by_cases hij : i = j
  · subst j
    simpa [entryCoefficient, entryOrder, Matrix.sub_apply] using
      entry_isBigO (exp_sub_one_isBigO L) i i
  · simpa only [entryCoefficient, entryOrder, if_neg hij, pow_one] using
      exp_entry_sub_linear_isBigO L i j hij

def offDiagonalCount {I : Type*} [Fintype I] (e : I → V × V) : ℕ :=
  ∑ k, entryOrder (e k).1 (e k).2

theorem offDiagonalCount_eq_card {I : Type*} [Fintype I] (e : I → V × V) :
    offDiagonalCount e = (Finset.univ.filter (fun k => (e k).1 ≠ (e k).2)).card := by
  classical
  simp [offDiagonalCount, entryOrder, Finset.card_filter]

/-- Diagonal positions contribute exactly one to the leading coefficient. -/
theorem productCoefficient_eq_offDiagonal (L : Matrix V V ℝ)
    {I : Type*} [Fintype I] (e : I → V × V) :
    (∏ k, entryCoefficient L (e k).1 (e k).2) =
      ∏ k ∈ Finset.univ.filter (fun k => (e k).1 ≠ (e k).2), L (e k).1 (e k).2 := by
  classical
  simp only [Finset.prod_filter, entryCoefficient, ne_eq, ite_not]

/-- The coefficient of a finite product is nonzero even when individual
logarithmic entries have mixed signs. -/
theorem productCoefficient_ne_zero (L : Matrix V V ℝ)
    (hfull : ∀ i j, i ≠ j → L i j ≠ 0)
    {I : Type*} [Fintype I] (e : I → V × V) :
    (∏ k, entryCoefficient L (e k).1 (e k).2) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => entryCoefficient_ne_zero L hfull _ _)

theorem exp_product_leading_isBigO (L : Matrix V V ℝ)
    {I : Type*} [Fintype I] (e : I → V × V) :
    (fun t => (∏ k, NormedSpace.exp ℝ (t • L) (e k).1 (e k).2) -
      (∏ k, entryCoefficient L (e k).1 (e k).2) * t ^ offDiagonalCount e)
      =O[𝓝 0] (fun t : ℝ => t ^ (offDiagonalCount e + 1)) := by
  exact finset_prod_leading_isBigO Finset.univ _ _ _ (fun k _ => exp_entry_leading_isBigO L _ _)

/-- Equal exponential products have equal numbers of off-diagonal positions.
The conclusion only needs equality near zero, and allows different index types. -/
theorem offDiagonalCount_eq_of_exp_products_eq (L : Matrix V V ℝ)
    (hfull : ∀ i j, i ≠ j → L i j ≠ 0)
    {I J : Type*} [Fintype I] [Fintype J] (e : I → V × V) (f : J → V × V)
    (heq : ∀ᶠ t : ℝ in 𝓝 0,
      (∏ k, NormedSpace.exp ℝ (t • L) (e k).1 (e k).2) =
        ∏ k, NormedSpace.exp ℝ (t • L) (f k).1 (f k).2) :
    offDiagonalCount e = offDiagonalCount f := by
  have hf := exp_product_leading_isBigO L f
  have hf' :
      (fun t => (∏ k, NormedSpace.exp ℝ (t • L) (e k).1 (e k).2) -
        (∏ k, entryCoefficient L (f k).1 (f k).2) * t ^ offDiagonalCount f)
        =O[𝓝 0] (fun t : ℝ => t ^ (offDiagonalCount f + 1)) := by
    apply hf.congr'
    · filter_upwards [heq] with t ht
      rw [ht]
    · rfl
  exact leading_order_unique _ _ _ _ (productCoefficient_ne_zero L hfull e)
    (productCoefficient_ne_zero L hfull f) (exp_product_leading_isBigO L e) hf'

/-- The product of target entries is exactly 2 to the number of diagonal positions. -/
theorem potts_product {I : Type*} [Fintype I] (e : I → V × V) :
    (∏ k, (pottsMatrix : Matrix V V ℝ) (e k).1 (e k).2) =
      2 ^ (Fintype.card I - offDiagonalCount e) := by
  classical
  have hsum : (∑ k : I, if (e k).1 = (e k).2 then 1 else 0) + offDiagonalCount e =
      Fintype.card I := by
    rw [offDiagonalCount, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _k : I, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : (e k).1 = (e k).2 <;> simp [entryOrder, h]
      _ = _ := by simp
  have he : ∀ k : I, (pottsMatrix : Matrix V V ℝ) (e k).1 (e k).2 =
      2 ^ (if (e k).1 = (e k).2 then 1 else 0 : ℕ) := by
    intro k
    by_cases h : (e k).1 = (e k).2 <;> simp [pottsMatrix, h]
  simp_rw [he, Finset.prod_pow_eq_pow_sum]
  congr 1
  omega

theorem potts_products_eq_of_exp_products_eq (L : Matrix V V ℝ)
    (hfull : ∀ i j, i ≠ j → L i j ≠ 0)
    {I J : Type*} [Fintype I] [Fintype J] (e : I → V × V) (f : J → V × V)
    (hcard : Fintype.card I = Fintype.card J)
    (heq : ∀ᶠ t : ℝ in 𝓝 0,
      (∏ k, NormedSpace.exp ℝ (t • L) (e k).1 (e k).2) =
        ∏ k, NormedSpace.exp ℝ (t • L) (f k).1 (f k).2) :
    (∏ k, (pottsMatrix : Matrix V V ℝ) (e k).1 (e k).2) =
      ∏ k, (pottsMatrix : Matrix V V ℝ) (f k).1 (f k).2 := by
  rw [potts_product, potts_product, hcard, offDiagonalCount_eq_of_exp_products_eq L hfull e f heq]

/-- Literal source condition 3.10(iv) for the actual spectral-power family. -/
theorem productIdentities {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.PosDef)
    (hfull : ∀ i j, i ≠ j → EntropyCompletion.matrixLog A i j ≠ 0) :
    ProductIdentities (SpectralProductZeros.realPower A) pottsMatrix := by
  intro m _ a b ha hb he
  let e : (Σ u : Upper q, Fin (a u)) → Fin q × Fin q := fun k => k.1.val
  let f : (Σ u : Upper q, Fin (b u)) → Fin q × Fin q := fun k => k.1.val
  have hprod (t : ℝ) :
      (∏ k, NormedSpace.exp ℝ (t • EntropyCompletion.matrixLog A) (e k).1 (e k).2) =
        ∏ k, NormedSpace.exp ℝ (t • EntropyCompletion.matrixLog A) (f k).1 (f k).2 := by
    have h := congrFun he t
    simp only [SpectralProductZeros.realPower_eq_exp_smul_log A hA t] at h
    simpa only [e, f, Fintype.prod_sigma, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using h
  have hcard : Fintype.card (Σ u : Upper q, Fin (a u)) =
      Fintype.card (Σ u : Upper q, Fin (b u)) := by
    simp only [Fintype.card_sigma, Fintype.card_fin, ha, hb]
  have h := potts_products_eq_of_exp_products_eq (EntropyCompletion.matrixLog A) hfull e f hcard
    (Filter.Eventually.of_forall hprod)
  simpa only [e, f, Fintype.prod_sigma, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using h

end PlanarHom.FullLogarithmicProductIdentities
