import PlanarHom.MagnitudeSignParallelReduction
import PlanarHom.ParallelSquareReduction
import PlanarHom.HomogeneousProductReductions
import PlanarHom.PositiveUnaryPowerField

/-! Exact field-level mixed equivalence and both weighted support chains in
Corollary 3.2. All endpoints use the same original fixed field representation. -/
noncomputable section
namespace PlanarHom.MagnitudeSign
open Complexity Complexity.MixedCode ProductCompatibility
variable {K : IntermediateField ℚ ℝ} {q dimension u d : ℕ}

def support (x : K) : K := if x=0 then 0 else 1
def supportMatrix (M : Matrix (Fin q) (Fin q) K) : Matrix (Fin q) (Fin q) K := fun i j => support (M i j)

@[simp] theorem support_coe (x : K) : (support x : ℝ) = if (x : ℝ)=0 then 0 else 1 := by
  by_cases h : x=0
  · simp [support,h]
  · have hz : (x : ℝ)≠0 := by exact_mod_cast h
    simp [support,h,hz]

@[simp] theorem magnitude_eq_zero (x : K) : magnitude x=0 ↔ x=0 := by
  unfold magnitude
  split <;> simp

private theorem magnitude_maps {I : Type} (A : I → K) : HasProductMaps A (fun i => magnitude (A i)) := by
  apply hasProductMaps_of_compatible
  apply compatible_of_field_embedding K.val.toRingHom
  have h : Compatible (fun i => (A i : ℝ)) (fun i => (magnitude (A i) : ℝ)) := by
    simpa only [magnitude_coe] using compatible_abs (fun i => (A i : ℝ))
  exact h

private theorem sign_maps {I : Type} (A : I → K) : HasProductMaps A (fun i => sign (A i)) := by
  apply hasProductMaps_of_compatible
  apply compatible_of_field_embedding K.val.toRingHom
  have h : Compatible (fun i => (A i : ℝ)) (fun i => (sign (A i) : ℝ)) := by
    simpa only [sign_coe] using compatible_sign (fun i => (A i : ℝ))
  exact h

private theorem support_maps {I : Type} (A : I → K) : HasProductMaps A (fun i => support (A i)) := by
  apply hasProductMaps_of_compatible
  apply compatible_of_field_embedding K.val.toRingHom
  have h : Compatible (fun i => (A i : ℝ)) (fun i => (support (A i) : ℝ)) := by
    simpa only [support_coe, supportTransform] using compatible_support (fun i => (A i : ℝ))
  exact h

private theorem mixed_zero (M : Matrix (Fin q) (Fin q) K) :
    ∀ l i j, M i j=0 → mixedLanguage M l i j=0 := by
  intro l i j h
  fin_cases l
  · change magnitude (M i j)=0
    exact (magnitude_eq_zero _).mpr h
  · change sign (M i j)=0
    simp [sign,h]

private theorem mixed_maps (M : Matrix (Fin q) (Fin q) K) :
    ∀ l, HasProductMaps (fun p : Fin q × Fin q => M p.1 p.2) (fun p => mixedLanguage M l p.1 p.2) := by
  intro l
  fin_cases l
  · exact magnitude_maps _
  · exact sign_maps _

def forwardMixedReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (mixedLanguage M) U w)
      (evaluationProblem basis (fun _ : Fin 1 => M) U w) :=
  finiteProductReduction basis M (mixedLanguage M) U w (mixed_zero M) (mixed_maps M)

def domainForwardMixedReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K)
    (D : Fin d → Set (Fin q)) (E : Fin d → Fin d → Prop) (T : Fin u → Fin d → Prop) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis (mixedLanguage M) U w D (fun _ => E) T)
      (domainEvaluationProblem basis (fun _ : Fin 1 => M) U w D (fun _ => E) T) :=
  domainFiniteProductReduction basis M (mixedLanguage M) U w D E T (mixed_zero M) (mixed_maps M)

theorem support_square (M : Matrix (Fin q) (Fin q) K) :
    supportMatrix (fun i j => M i j ^ 2)=supportMatrix M := by
  funext i j
  simp [supportMatrix,support,pow_eq_zero_iff]

theorem support_magnitude (M : Matrix (Fin q) (Fin q) K) :
    supportMatrix (magnitudeMatrix M)=supportMatrix M := by
  funext i j
  simp only [supportMatrix,magnitudeMatrix,support,magnitude_eq_zero]

def supportReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (fun _ : Fin 1 => supportMatrix M) U w)
      (evaluationProblem basis (fun _ : Fin 1 => M) U w) :=
  homogeneousProductReduction basis M (supportMatrix M) U w
    (by intro i j h; simp [supportMatrix,support,h]) (support_maps _)

def supportSquareReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (fun _ : Fin 1 => supportMatrix M) U w)
      (evaluationProblem basis (fun _ : Fin 1 => fun i j => M i j ^ 2) U w) := by
  rw [← support_square M]
  exact supportReduction basis (fun i j => M i j ^ 2) U w

def supportMagnitudeReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (fun _ : Fin 1 => supportMatrix M) U w)
      (evaluationProblem basis (fun _ : Fin 1 => magnitudeMatrix M) U w) := by
  rw [← support_magnitude M]
  exact supportReduction basis (magnitudeMatrix M) U w

def magnitudeReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (fun _ : Fin 1 => magnitudeMatrix M) U w)
      (evaluationProblem basis (fun _ : Fin 1 => M) U w) :=
  homogeneousProductReduction basis M (magnitudeMatrix M) U w
    (by intro i j h; exact (magnitude_eq_zero _).mpr h) (magnitude_maps _)

end PlanarHom.MagnitudeSign
