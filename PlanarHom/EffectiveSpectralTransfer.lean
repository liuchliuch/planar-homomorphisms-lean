import PlanarHom.EffectivePolynomialTransfer
import PlanarHom.SpectralPowerEvaluationMachines

/-! Source Lemma3.10(S), fixed target: genuine spectral zero bounds, actual
integer matrix-power evaluation, finite sample search and charged oracle reduction. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.EffectiveProductTransfer
open Complexity Complexity.MixedCode FiniteLanguageAliases
open ExponentProductSemantics ExponentProductTables SymmetricProductIdentities
open SpectralProductZeros
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {q bt ut dimension : ℕ}

def matrixPowerRealFamily (A : Matrix (Fin q) (Fin q) K) (x : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  realPower (SpectralFieldPresentation.realMatrix A) x

theorem realPower_nat (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.IsHermitian) (n : ℕ) :
    realPower A n = A ^ n := by
  unfold realPower
  simpa only [Real.rpow_natCast] using (cfc_pow_id (R := ℝ) A n hA)

omit [FiniteDimensional ℚ K] in
@[simp] theorem matrixPowerFamily_coe (A : Matrix (Fin q) (Fin q) K)
    (hA : (SpectralFieldPresentation.realMatrix A).IsHermitian) (n : ℕ) (i j : Fin q) :
    ((A ^ n) i j : ℝ) = matrixPowerRealFamily A n i j := by
  rw [matrixPowerRealFamily, realPower_nat _ hA]
  have h := congrArg (fun N => N i j) (map_pow K.val.toRingHom.mapMatrix A n)
  exact h

omit [FiniteDimensional ℚ K] in
theorem matrixPowerRealFamily_symm (A : Matrix (Fin q) (Fin q) K) (x : ℝ) (i j : Fin q) :
    matrixPowerRealFamily A x i j = matrixPowerRealFamily A x j i := by
  have h : (matrixPowerRealFamily A x).IsHermitian :=
    cfc_predicate (fun y : ℝ => y ^ x) (SpectralFieldPresentation.realMatrix A)
  simpa using h.apply j i

def spectralCandidateCount (q s : ℕ) : Polynomial ℕ :=
  ((Polynomial.X + 1) ^ (q * q)) ^ 2 * (Polynomial.X + 1) ^ s + 1

@[simp] theorem spectralCandidateCount_eval (q s m : ℕ) :
    (spectralCandidateCount q s).eval m = ((m + 1) ^ (q * q)) ^ 2 * (m + 1) ^ s + 1 := by
  simp [spectralCandidateCount]

omit [FiniteDimensional ℚ K] in
theorem spectral_samples (A B : Matrix (Fin q) (Fin q) K)
    (hA : (SpectralFieldPresentation.realMatrix A).PosDef) (n₀ : ℕ)
    (hBsym : ∀ i j, B i j = B j i)
    (hidentity : ProductIdentities (matrixPowerRealFamily A) (fun i j => (B i j : ℝ))) :
    ∀ m, ∃ j < (spectralCandidateCount q
      (Nat.card (spectrum ℝ (SpectralFieldPresentation.realMatrix A)))).eval m,
      CompatibleAt (binaryAlphabet (A ^ (n₀ + j))) (binaryAlphabet B) m := by
  intro m
  by_cases hm : m = 0
  · subst m
    exact ⟨0, by simp, compatibleAt_zero _ _⟩
  have hord := ordered_identity_of_upper (matrixPowerRealFamily A) (fun i j => (B i j : ℝ))
    (matrixPowerRealFamily_symm A) (fun i j => congrArg (fun x : K => (x : ℝ)) (hBsym i j))
    (hidentity m (by omega))
  obtain ⟨n, hn, hb, hc⟩ := matrixPower_exists_compatible_sample
    (SpectralFieldPresentation.realMatrix A) (fun i j => (B i j : ℝ)) hA m n₀ hord
  refine ⟨n - n₀, ?_, ?_⟩
  · rw [spectralCandidateCount_eval]
    omega
  · have he : n₀ + (n - n₀) = n := by omega
    rw [he]
    apply (FieldProductSampling.compatibleAt_iff_map K.val.toRingHom _ _ m).mpr
    convert hc using 1
    funext e
    exact matrixPowerFamily_coe A hA.1 n _ _

/-- Complete fixed-target spectral-family transfer, retaining all old labels,
original source answers, and the supplied uniform family simulation. -/
def spectral_reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (A B : Matrix (Fin q) (Fin q) K)
    (hA : (SpectralFieldPresentation.realMatrix A).PosDef)
    (hBsym : ∀ i j, B i j = B j i) (n₀ : ℕ) (hn₀ : 1 ≤ n₀)
    (hpositive : ∀ n, n₀ ≤ n → ∀ i j, 0 < matrixPowerRealFamily A n i j)
    (hidentity : ProductIdentities (matrixPowerRealFamily A) (fun i j => (B i j : ℝ)))
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (DynamicMatrixFamilySource.problem basis M U (fun _ => 1) (fun n => A ^ n)) base) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (appendOne M B) U (fun _ => 1)) base := by
  apply DynamicMatrixFamilyReduction.reduction basis M U (fun _ => 1)
    (fun n => A ^ n) B n₀ hn₀
    (spectralCandidateCount q (Nat.card (spectrum ℝ (SpectralFieldPresentation.realMatrix A))))
  · exact SpectralPowerEvaluationMachines.fp_matrixPowers basis A hA.1
  · intro n hn i j hz
    have hp := hpositive n hn i j
    rw [← matrixPowerFamily_coe A hA.1, hz] at hp
    exact lt_irrefl 0 hp
  · exact spectral_samples A B hA n₀ hBsym hidentity
  · exact simulation

end PlanarHom.EffectiveProductTransfer
