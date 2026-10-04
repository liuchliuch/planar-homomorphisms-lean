import PlanarHom.RealApproximationRepresented
import PlanarHom.FixedRealFiniteReplacement
import PlanarHom.MagnitudeExtremaCompatibility
import PlanarHom.MagnitudeSignParallelReduction

/-! NEW represented A.7 transforms in the actual prescribed field. Signs and
comparisons here select fixed matrix constants, never variable-real oracles. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealSignedTransforms
open DensePolynomial FixedRealExtension Complexity Complexity.MixedCode RepresentedBit ProductCompatibility
variable {n e q u : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]
variable (φ : K →+* ℝ)

def support (x : K) : K := if x = 0 then 0 else 1
def magnitude (x : K) : K := if φ x < 0 then -x else x
def sign (x : K) : K := if x = 0 then 0 else if φ x < 0 then -1 else 1

@[simp] theorem support_image (x : K) : φ (support x) = if φ x = 0 then 0 else 1 := by
  by_cases h : x = 0 <;> simp [support,h]
@[simp] theorem magnitude_image (x : K) : φ (magnitude φ x) = |φ x| := by
  by_cases h : φ x < 0
  · simp [magnitude,h,abs_of_neg h]
  · simp [magnitude,h,abs_of_nonneg (le_of_not_gt h)]
@[simp] theorem sign_image (x : K) : φ (sign φ x) = Real.sign (φ x) := by
  by_cases hz : x = 0
  · simp [sign,hz]
  · have hφ : φ x ≠ 0 := (map_ne_zero φ).mpr hz
    by_cases hn : φ x < 0
    · simp [sign,hz,hn,Real.sign_of_neg hn]
    · have hp : 0 < φ x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hφ)
      simp [sign,hz,hn,Real.sign_of_pos hp]

theorem magnitude_mul_sign (x : K) : magnitude φ x * sign φ x = x := by
  apply φ.injective
  rw [map_mul,magnitude_image,sign_image,abs_mul_real_sign]

theorem magnitude_maps {I : Type} (A : I → K) : HasProductMaps A (fun i => magnitude φ (A i)) := by
  apply hasProductMaps_of_compatible
  apply Compatible.of_injective_map φ
  simpa only [magnitude_image] using compatible_abs (fun i => φ (A i))

theorem sign_maps {I : Type} (A : I → K) : HasProductMaps A (fun i => sign φ (A i)) := by
  apply hasProductMaps_of_compatible
  apply Compatible.of_injective_map φ
  simpa only [sign_image] using compatible_sign (fun i => φ (A i))

include φ in
theorem support_maps {I : Type} (A : I → K) : HasProductMaps A (fun i => support (A i)) := by
  apply hasProductMaps_of_compatible
  apply Compatible.of_injective_map φ
  simpa only [support_image,supportTransform] using compatible_support (fun i => φ (A i))

def transform (M : Matrix (Fin q) (Fin q) K) : Fin 3 → Matrix (Fin q) (Fin q) K :=
  fun l i j => if l = 0 then support (M i j) else if l = 1 then magnitude φ (M i j) else sign φ (M i j)

def theoremA7_joint (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K) :
    Reduction (FixedRealMixedInterpolation.problem basis (transform φ M) U w)
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M) U w) := by
  apply FixedRealMixedInterpolation.finiteReplacementReduction basis M (transform φ M) U w
  · intro l i j h
    fin_cases l <;> simp [transform,support,magnitude,sign,h]
  · intro l
    fin_cases l
    · simpa [transform] using support_maps φ (fun p : Fin q × Fin q => M p.1 p.2)
    · simpa [transform] using magnitude_maps φ (fun p : Fin q × Fin q => M p.1 p.2)
    · simpa [transform] using sign_maps φ (fun p : Fin q × Fin q => M p.1 p.2)

def supportReduction (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K) :
    Reduction (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => fun i j => support (M i j)) U w)
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M) U w) :=
  FixedRealMixedInterpolation.finiteReplacementReduction basis M _ U w
    (fun _ _ _ h => by simp [support,h]) (fun _ => support_maps φ _)

def magnitudeReduction (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K) :
    Reduction (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => fun i j => magnitude φ (M i j)) U w)
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M) U w) :=
  FixedRealMixedInterpolation.finiteReplacementReduction basis M _ U w
    (fun _ _ _ h => by simp [magnitude,h]) (fun _ => magnitude_maps φ _)

def mixed (M : Matrix (Fin q) (Fin q) K) : Fin 2 → Matrix (Fin q) (Fin q) K :=
  twoFactorLanguage (fun i j => magnitude φ (M i j)) (fun i j => sign φ (M i j))

def forwardMixedReduction (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K) :
    Reduction (FixedRealMixedInterpolation.problem basis (mixed φ M) U w)
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M) U w) := by
  apply FixedRealMixedInterpolation.finiteReplacementReduction basis M _ U w
  · intro l i j h
    fin_cases l <;> simp [mixed,twoFactorLanguage,magnitude,sign,h]
  · intro l
    fin_cases l
    · simpa [mixed,twoFactorLanguage] using magnitude_maps φ (fun p : Fin q × Fin q => M p.1 p.2)
    · simpa [mixed,twoFactorLanguage] using sign_maps φ (fun p : Fin q × Fin q => M p.1 p.2)

def reverseMixedReduction (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K) :
    Reduction (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M) U w)
      (FixedRealMixedInterpolation.problem basis (mixed φ M) U w) := by
  let table := FiniteLabelWordLookupMachines.finTable twoFactorWord
  apply queryReduction (presentation basis) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
    (PlanarValid 1 u) (PlanarValid 2 u) _ _ (expandBinaryWords table)
    (fp_expandBinaryWords table)
  · intro g hg
    exact expandBinaryWords_planar table hg (FiniteLabelWordLookupMachines.lookup_finTable_lt twoFactorWord)
  · intro g hg
    rw [totalEvaluation_valid _ _ _ g hg.1,totalEvaluation_valid _ _ _ _
      (expandBinaryWords_valid table hg.1 (FiniteLabelWordLookupMachines.lookup_finTable_lt twoFactorWord))]
    have hword : wordMatrices twoFactorWord (mixed φ M) = (fun _ : Fin 1 => M) := by
      funext l i j
      simp [wordMatrices,twoFactorWord,mixed,twoFactorLanguage,magnitude_mul_sign]
    simpa only [hword,table] using evaluate_expandBinaryWords g hg.1 twoFactorWord (mixed φ M) U w

end PlanarHom.FixedRealSignedTransforms
