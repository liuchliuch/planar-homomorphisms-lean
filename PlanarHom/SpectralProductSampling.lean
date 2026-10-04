import PlanarHom.SpectralProductZeros
import PlanarHom.ProductFamilySampling

/-! The exact spectral stars-and-bars zero bound supplies the bounded integer
sample in Lemma3.10, for actual positive-definite matrix real powers. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.SpectralProductZeros
open ExponentProductSemantics ExponentProductTables

/-- Counting multiplicities injects a symmetric m-tuple into s bounded counters. -/
theorem sym_card_le_power (s m : ℕ) : Fintype.card (Sym (Fin s) m) ≤ (m + 1) ^ s := by
  let f : Sym (Fin s) m → Fin s → Fin (m + 1) := fun u i =>
    ⟨u.val.count i, by have h := Multiset.count_le_card i u.val; rw [u.property] at h; omega⟩
  have hf : Function.Injective f := by
    intro u v h
    apply Sym.ext
    apply Multiset.ext.mpr
    intro i
    exact congrArg Fin.val (congrFun h i)
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fun, Fintype.card_fin] using h

/-- The exact source zero bound has a fixed-degree polynomial upper bound in m. -/
theorem choose_bound_le_power (s m : ℕ) :
    (s + m - 1).choose m - 1 ≤ (m + 1) ^ s := by
  have h := sym_card_le_power s m
  rw [Sym.card_sym_eq_choose, Fintype.card_fin] at h
  omega

/-- Products specified by exact weak exponent vectors have the genuine spectral
zero bound; expansion into words is a proof device, not an algorithmic step. -/
theorem spectral_agreementBound {s t : ℕ} (μ : Fin s → ℝ) (hμ : ∀ i, 0 < μ i)
    (c : Fin t → Fin s → ℝ) (m : ℕ) :
    ProductFamilySampling.AgreementBound
      (fun x e => ∑ i, c e i * μ i ^ x) m ((s + m - 1).choose m - 1) := by
  intro xs hxs ys hys hne T hT
  obtain ⟨hxl, hxm⟩ := (ExponentVectors.mem_weak t m xs).mp hxs
  obtain ⟨hyl, hym⟩ := (ExponentVectors.mem_weak t m ys).mp hys
  have hx : (expand t xs).length = m := (expand_length xs hxl).trans hxm
  have hy : (expand t ys).length = m := (expand_length ys hyl).trans hym
  have h := product_agreement_card_le μ hμ c (expand t xs) (expand t ys) (hx.trans hy.symm)
    (by simpa only [expand_product] using hne) T (by simpa only [expand_product] using hT)
  simpa only [hx] using h

variable {q : ℕ}

/-- Source (3.5), with its exact distinct-eigenvalue count and actual CFC family. -/
theorem matrixPower_agreementBound (M : Matrix (Fin q) (Fin q) ℝ) (hM : M.PosDef) (m : ℕ) :
    ProductFamilySampling.AgreementBound
      (fun x => Complexity.MixedCode.binaryAlphabet (realPower M x)) m
      ((Nat.card (spectrum ℝ M) + m - 1).choose m - 1) := by
  have h := spectral_agreementBound (RealSpectralInterpolation.scalar M)
    (RealSpectralInterpolation.scalar_pos M hM)
    (fun e : Fin (q * q) => fun i => RealSpectralInterpolation.projector M i
      (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2) m
  convert h using 1
  funext x e
  exact realPower_entry M x _ _

/-- One polynomially bounded integer gives exactly the compatibility needed by
the current input's Vandermonde recovery. Signed/zero targets are admitted. -/
theorem matrixPower_exists_compatible_sample (M B : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.PosDef) (m n₀ : ℕ)
    (hidentity : ∀ xs ∈ ExponentVectors.weak (q * q) m,
      ∀ ys ∈ ExponentVectors.weak (q * q) m,
      (fun x => value (Complexity.MixedCode.binaryAlphabet (realPower M x)) xs) =
        (fun x => value (Complexity.MixedCode.binaryAlphabet (realPower M x)) ys) →
      value (Complexity.MixedCode.binaryAlphabet B) xs =
        value (Complexity.MixedCode.binaryAlphabet B) ys) :
    ∃ n, n₀ ≤ n ∧ n ≤ n₀ + ((m + 1) ^ (q * q)) ^ 2 *
      (m + 1) ^ Nat.card (spectrum ℝ M) ∧
      CompatibleAt (Complexity.MixedCode.binaryAlphabet (realPower M n))
        (Complexity.MixedCode.binaryAlphabet B) m := by
  obtain ⟨n, hn, hb, hc⟩ := ProductFamilySampling.exists_compatible_sample
    (fun x => Complexity.MixedCode.binaryAlphabet (realPower M x))
    (Complexity.MixedCode.binaryAlphabet B) m _ n₀ (matrixPower_agreementBound M hM m) hidentity
  exact ⟨n, hn, hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _
    (choose_bound_le_power (Nat.card (spectrum ℝ M)) m)) n₀), hc⟩

end PlanarHom.SpectralProductZeros
