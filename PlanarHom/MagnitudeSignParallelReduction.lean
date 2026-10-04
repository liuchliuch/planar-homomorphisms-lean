import PlanarHom.MixedLabelExpansionReductions
import PlanarHom.SupportTransformCompatibility

/-! The reverse direction of the mixed equivalence in Corollary 3.2: every
M-occurrence is replaced by one magnitude and one sign occurrence in parallel.
The same construction handles loops and retains every vertex/background factor. -/
noncomputable section
namespace PlanarHom.Complexity.MixedCode
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension u d : ℕ}

def twoFactorWord : Fin 1→List (Fin 2) := fun _ => [0,1]

def twoFactorLanguage (A B : Matrix C C K) : Fin 2→Matrix C C K :=
  fun i => if i=0 then A else B

@[simp] theorem twoFactorLanguage_zero (A B : Matrix C C K) : twoFactorLanguage A B 0=A := by
  simp [twoFactorLanguage]

@[simp] theorem twoFactorLanguage_one (A B : Matrix C C K) : twoFactorLanguage A B 1=B := by
  simp [twoFactorLanguage]

theorem wordMatrices_twoFactor (A B : Matrix C C K) :
    wordMatrices twoFactorWord (twoFactorLanguage A B)=fun _ : Fin 1 => fun x y => A x y * B x y := by
  funext i x y
  simp [wordMatrices,twoFactorWord,twoFactorLanguage]

/-- One actual mixed oracle call computes the pointwise product language. -/
def twoFactorReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (A B : Matrix C C K) (U : Fin u→C→K) (w : C→K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (fun _ : Fin 1 => fun x y => A x y * B x y) U w)
      (evaluationProblem basis (twoFactorLanguage A B) U w) := by
  simpa only [wordMatrices_twoFactor] using binaryWordExpansionReduction basis twoFactorWord
    (twoFactorLanguage A B) U w

def domainTwoFactorReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (A B : Matrix C C K) (U : Fin u→C→K) (w : C→K) (D : Fin d→Set C)
    (E : Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (fun _ : Fin 1 => fun x y => A x y * B x y) U w D (fun _ => E) T)
      (domainEvaluationProblem basis (twoFactorLanguage A B) U w D (fun _ => E) T) := by
  simpa only [wordMatrices_twoFactor] using domainBinaryWordExpansionReduction basis twoFactorWord
    (twoFactorLanguage A B) U w D (fun _ => E) (fun _ => E) T (fun _ _ _ h _ _ => h)

end PlanarHom.Complexity.MixedCode

namespace PlanarHom.MagnitudeSign
variable {C : Type} [Fintype C] {K : IntermediateField ℚ ℝ}
variable {dimension u d : ℕ}

/-- Absolute value lies in the original real number field; no field extension
or new value oracle is needed. -/
def magnitude (x : K) : K := if (x : ℝ)<0 then -x else x

def sign (x : K) : K := if x=0 then 0 else if (x : ℝ)<0 then -1 else 1

@[simp] theorem magnitude_coe (x : K) : (magnitude x : ℝ)=|(x : ℝ)| := by
  by_cases h : (x : ℝ)<0
  · simp [magnitude,h,abs_of_neg h]
  · simp [magnitude,h,abs_of_nonneg (le_of_not_gt h)]

@[simp] theorem sign_coe (x : K) : (sign x : ℝ)=Real.sign (x : ℝ) := by
  by_cases hz : x=0
  · simp [sign,hz]
  · have hz' : (x : ℝ)≠0 := by exact_mod_cast hz
    by_cases hn : (x : ℝ)<0
    · simp [sign,hz,hn,Real.sign_of_neg hn]
    · have hp : 0<(x : ℝ) := lt_of_le_of_ne (le_of_not_gt hn) hz'.symm
      simp [sign,hz,hn,Real.sign_of_pos hp]

theorem magnitude_mul_sign (x : K) : magnitude x * sign x=x := by
  apply Subtype.ext
  change (magnitude x : ℝ)*(sign x : ℝ)=(x : ℝ)
  rw [magnitude_coe,sign_coe,ProductCompatibility.abs_mul_real_sign]

def magnitudeMatrix (M : Matrix C C K) : Matrix C C K := fun i j => magnitude (M i j)
def signMatrix (M : Matrix C C K) : Matrix C C K := fun i j => sign (M i j)

def mixedLanguage (M : Matrix C C K) : Fin 2→Matrix C C K :=
  Complexity.MixedCode.twoFactorLanguage (magnitudeMatrix M) (signMatrix M)

@[simp] theorem mixedLanguage_zero_coe (M : Matrix C C K) (i j : C) :
    (mixedLanguage M 0 i j : ℝ)=|(M i j : ℝ)| := by
  simp [mixedLanguage,magnitudeMatrix]

@[simp] theorem mixedLanguage_one_coe (M : Matrix C C K) (i j : C) :
    (mixedLanguage M 1 i j : ℝ)=Real.sign (M i j : ℝ) := by
  simp [mixedLanguage,signMatrix]

theorem factorization (M : Matrix C C K) :
    (fun i j => magnitudeMatrix M i j * signMatrix M i j)=M := by
  funext i j
  exact magnitude_mul_sign _

open Complexity Complexity.MixedCode

theorem evaluate_parallel_pair (M : Matrix C C K) (U : Fin u→C→K) (w : C→K)
    (g : MixedCode) (hg : g.Valid 1 u) :
    (g.expandBinaryWords (FiniteLabelWordLookupMachines.finTable twoFactorWord)).evaluate
      (expandBinaryWords_valid _ hg (FiniteLabelWordLookupMachines.lookup_finTable_lt twoFactorWord))
      (mixedLanguage M) U w=g.evaluate hg (fun _ : Fin 1 => M) U w := by
  simpa only [mixedLanguage,wordMatrices_twoFactor,magnitudeMatrix,signMatrix,magnitude_mul_sign] using
    evaluate_expandBinaryWords g hg twoFactorWord (mixedLanguage M) U w

/-- Genuine raw promise reduction to the two-type mixed problem, with one
magnitude edge and one sign edge for each original binary occurrence. -/
def reverseMixedReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (U : Fin u→C→K) (w : C→K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (fun _ : Fin 1 => M) U w)
      (evaluationProblem basis (mixedLanguage M) U w) := by
  simpa only [magnitudeMatrix,signMatrix,magnitude_mul_sign,mixedLanguage] using twoFactorReduction basis
    (magnitudeMatrix M) (signMatrix M) U w

/-- The same single query preserves the prescribed domain assignment, ordinary
unaries, reserved indicators and arbitrary fixed background weights. -/
def domainReverseMixedReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (U : Fin u→C→K) (w : C→K) (D : Fin d→Set C)
    (E : Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (fun _ : Fin 1 => M) U w D (fun _ => E) T)
      (domainEvaluationProblem basis (mixedLanguage M) U w D (fun _ => E) T) := by
  simpa only [magnitudeMatrix,signMatrix,magnitude_mul_sign,mixedLanguage] using domainTwoFactorReduction basis
    (magnitudeMatrix M) (signMatrix M) U w D E T

end PlanarHom.MagnitudeSign
