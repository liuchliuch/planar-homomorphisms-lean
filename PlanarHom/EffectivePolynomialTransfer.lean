import PlanarHom.DynamicMatrixFamilyReduction
import PlanarHom.FixedFieldPolynomialMachines
import PlanarHom.FieldProductSampling
import PlanarHom.SymmetricProductIdentities

/-! Source Lemma3.10(P), fixed target: a complete actual bit-reduction endpoint.
The upper-triangular identity condition, positivity threshold and one uniform
source simulator are exactly explicit source hypotheses. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.EffectiveProductTransfer
open Complexity Complexity.MixedCode FiniteLanguageAliases
open ExponentProductSemantics ExponentProductTables SymmetricProductIdentities
variable {q bt ut dimension : ℕ}

/-- Literal condition(iv), with the paper's upper-triangular alphabet and
positive common factor count. -/
def ProductIdentities (F : ℝ → Matrix (Fin q) (Fin q) ℝ)
    (B : Matrix (Fin q) (Fin q) ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ a b : Upper q → ℕ,
    (∑ e, a e) = m → (∑ e, b e) = m →
    (fun x : ℝ => ∏ e, F x e.val.1 e.val.2 ^ a e) =
      (fun x : ℝ => ∏ e, F x e.val.1 e.val.2 ^ b e) →
    (∏ e, B e.val.1 e.val.2 ^ a e) = ∏ e, B e.val.1 e.val.2 ^ b e

/-- The missing m=0 clause is automatic and imposes no source condition. -/
theorem compatibleAt_zero {K : Type} [Field K] {t : ℕ} (A B : Fin t → K) :
    CompatibleAt A B 0 := by
  intro xs hxs ys hys _ _
  have hv (zs : List ℕ) (hzs : zs ∈ ExponentVectors.weak t 0) : value B zs = 1 := by
    obtain ⟨hl, hs⟩ := (ExponentVectors.mem_weak t 0 zs).mp hzs
    have he : expand t zs = [] := List.length_eq_zero_iff.mp ((expand_length zs hl).trans hs)
    rw [← expand_product, he]
    rfl
  rw [hv xs hxs, hv ys hys]

variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]

def polynomialFamily (F : Matrix (Fin q) (Fin q) (Polynomial K))
    (n : ℕ) : Matrix (Fin q) (Fin q) K := fun i j => (F i j).eval (n : K)

def polynomialRealFamily (F : Matrix (Fin q) (Fin q) (Polynomial K))
    (x : ℝ) : Matrix (Fin q) (Fin q) ℝ := fun i j => ((F i j).map K.val.toRingHom).eval x

omit [FiniteDimensional ℚ K] in
@[simp] theorem polynomialFamily_coe (F : Matrix (Fin q) (Fin q) (Polynomial K))
    (n : ℕ) (i j : Fin q) :
    (polynomialFamily F n i j : ℝ) = polynomialRealFamily F n i j := by
  change K.val.toRingHom ((F i j).eval (n : K)) = ((F i j).map K.val.toRingHom).eval (n : ℝ)
  rw [Polynomial.eval_map]
  simpa only [map_natCast] using (Polynomial.eval₂_at_apply (p := F i j) K.val.toRingHom (n : K)).symm

def polynomialCandidateCount (q d : ℕ) : Polynomial ℕ :=
  ((Polynomial.X + 1) ^ (q * q)) ^ 2 * (Polynomial.C d * Polynomial.X) + 1

@[simp] theorem polynomialCandidateCount_eval (q d m : ℕ) :
    (polynomialCandidateCount q d).eval m = ((m + 1) ^ (q * q)) ^ 2 * (d * m) + 1 := by
  simp [polynomialCandidateCount]

omit [FiniteDimensional ℚ K] in
/-- Every required mathematical sampling premise is derived from the actual
polynomial zero bound and the literal source product identities. -/
theorem polynomial_samples (F : Matrix (Fin q) (Fin q) (Polynomial K))
    (B : Matrix (Fin q) (Fin q) K) (d n₀ : ℕ)
    (hdegree : ∀ i j, (F i j).natDegree ≤ d)
    (hFsym : ∀ x i j, polynomialRealFamily F x i j = polynomialRealFamily F x j i)
    (hBsym : ∀ i j, B i j = B j i)
    (hidentity : ProductIdentities (polynomialRealFamily F) (fun i j => (B i j : ℝ))) :
    ∀ m, ∃ j < (polynomialCandidateCount q d).eval m,
      CompatibleAt (binaryAlphabet (polynomialFamily F (n₀ + j))) (binaryAlphabet B) m := by
  intro m
  by_cases hm : m = 0
  · subst m
    exact ⟨0, by simp, compatibleAt_zero _ _⟩
  have hord := ordered_identity_of_upper (polynomialRealFamily F) (fun i j => (B i j : ℝ))
    hFsym (fun i j => congrArg (fun x : K => (x : ℝ)) (hBsym i j))
    (hidentity m (by omega))
  obtain ⟨n, hn, hb, hc⟩ := FieldProductSampling.polynomial_exists_compatible_sample K.val.toRingHom
    (fun e : Fin (q*q) => F (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2)
    (binaryAlphabet B) d m n₀ (fun e => hdegree _ _) (by
      intro xs hxs ys hys he
      apply K.val.injective
      rw [FieldProductSampling.map_value, FieldProductSampling.map_value]
      exact hord xs hxs ys hys he)
  refine ⟨n - n₀, ?_, ?_⟩
  · rw [polynomialCandidateCount_eval]
    omega
  · have he : n₀ + (n - n₀) = n := by omega
    rw [he]
    exact hc

/-- Complete fixed-target polynomial-family transfer. Old constraints coexist
with the replacement, and the original uniform simulator is the final oracle. -/
def polynomial_reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (F : Matrix (Fin q) (Fin q) (Polynomial K)) (B : Matrix (Fin q) (Fin q) K)
    (d n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hdegree : ∀ i j, (F i j).natDegree ≤ d)
    (hFsym : ∀ x i j, polynomialRealFamily F x i j = polynomialRealFamily F x j i)
    (hBsym : ∀ i j, B i j = B j i)
    (hpositive : ∀ n, n₀ ≤ n → ∀ i j, 0 < polynomialRealFamily F n i j)
    (hidentity : ProductIdentities (polynomialRealFamily F) (fun i j => (B i j : ℝ)))
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (DynamicMatrixFamilySource.problem basis M U (fun _ => 1) (polynomialFamily F)) base) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (appendOne M B) U (fun _ => 1)) base := by
  apply DynamicMatrixFamilyReduction.reduction basis M U (fun _ => 1)
    (polynomialFamily F) B n₀ hn₀ (polynomialCandidateCount q d)
  · exact FixedFieldPolynomialMachines.fp_polynomialFamily basis
      (fun e : Fin (q*q) => F (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2)
  · intro n hn i j hz
    have hp := hpositive n hn i j
    rw [← polynomialFamily_coe, hz] at hp
    exact lt_irrefl 0 hp
  · exact polynomial_samples F B d n₀ hdegree hFsym hBsym hidentity
  · exact simulation

end PlanarHom.EffectiveProductTransfer
