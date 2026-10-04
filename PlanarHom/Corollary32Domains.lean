import PlanarHom.Corollary32Real

/-! Prescribed-domain versions of both Corollary 3.2 support chains and mixed
equivalence. Every original domain assignment and intrinsic indicator is retained. -/
noncomputable section
namespace PlanarHom.MagnitudeSign
open Complexity Complexity.MixedCode
variable {K : IntermediateField ℚ ℝ} {q dimension u d : ℕ}

def domainSupportReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K)
    (D : Fin d → Set (Fin q)) (E : Fin d → Fin d → Prop) (T : Fin u → Fin d → Prop) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (fun _ : Fin 1 => supportMatrix M) U w D (fun _ => E) T)
      (domainEvaluationProblem basis (fun _ : Fin 1 => M) U w D (fun _ => E) T) := by
  have hmaps : ProductCompatibility.HasProductMaps (fun p : Fin q × Fin q => M p.1 p.2)
      (fun p => support (M p.1 p.2)) := by
    apply ProductCompatibility.hasProductMaps_of_compatible
    apply ProductCompatibility.compatible_of_field_embedding K.val.toRingHom
    have h : ProductCompatibility.Compatible (fun p : Fin q × Fin q => (M p.1 p.2 : ℝ))
        (fun p => (support (M p.1 p.2) : ℝ)) := by
      simpa only [support_coe, ProductCompatibility.supportTransform] using
        ProductCompatibility.compatible_support (fun p : Fin q × Fin q => (M p.1 p.2 : ℝ))
    exact h
  exact domainHomogeneousProductReduction basis M (supportMatrix M) U w D E T
    (by intro i j h; simp [supportMatrix,support,h]) hmaps

def domainSupportSquareReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K)
    (D : Fin d → Set (Fin q)) (E : Fin d → Fin d → Prop) (T : Fin u → Fin d → Prop) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (fun _ : Fin 1 => supportMatrix M) U w D (fun _ => E) T)
      (domainEvaluationProblem basis (fun _ : Fin 1 => fun i j => M i j ^ 2) U w D (fun _ => E) T) := by
  rw [← support_square M]
  exact domainSupportReduction basis (fun i j => M i j ^ 2) U w D E T

def domainSupportMagnitudeReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K)
    (D : Fin d → Set (Fin q)) (E : Fin d → Fin d → Prop) (T : Fin u → Fin d → Prop) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (fun _ : Fin 1 => supportMatrix M) U w D (fun _ => E) T)
      (domainEvaluationProblem basis (fun _ : Fin 1 => magnitudeMatrix M) U w D (fun _ => E) T) := by
  rw [← support_magnitude M]
  exact domainSupportReduction basis (magnitudeMatrix M) U w D E T

def domainMagnitudeReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K)
    (D : Fin d → Set (Fin q)) (E : Fin d → Fin d → Prop) (T : Fin u → Fin d → Prop) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (fun _ : Fin 1 => magnitudeMatrix M) U w D (fun _ => E) T)
      (domainEvaluationProblem basis (fun _ : Fin 1 => M) U w D (fun _ => E) T) := by
  have hmaps : ProductCompatibility.HasProductMaps (fun p : Fin q × Fin q => M p.1 p.2)
      (fun p => magnitude (M p.1 p.2)) := by
    apply ProductCompatibility.hasProductMaps_of_compatible
    apply ProductCompatibility.compatible_of_field_embedding K.val.toRingHom
    have h : ProductCompatibility.Compatible (fun p : Fin q × Fin q => (M p.1 p.2 : ℝ))
        (fun p => (magnitude (M p.1 p.2) : ℝ)) := by
      simpa only [magnitude_coe] using ProductCompatibility.compatible_abs (fun p : Fin q × Fin q => (M p.1 p.2 : ℝ))
    exact h
  exact domainHomogeneousProductReduction basis M (magnitudeMatrix M) U w D E T
    (by intro i j h; exact (magnitude_eq_zero _).mpr h) hmaps

theorem domain_mixed_equivalence (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K)
    (D : Fin d → Set (Fin q)) (E : Fin d → Fin d → Prop) (T : Fin u → Fin d → Prop) :
    Nonempty (PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (fun _ : Fin 1 => M) U w D (fun _ => E) T)
      (domainEvaluationProblem basis (mixedLanguage M) U w D (fun _ => E) T)) ∧
    Nonempty (PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (mixedLanguage M) U w D (fun _ => E) T)
      (domainEvaluationProblem basis (fun _ : Fin 1 => M) U w D (fun _ => E) T)) :=
  ⟨⟨domainReverseMixedReduction basis M U w D E T⟩, ⟨domainForwardMixedReduction basis M U w D E T⟩⟩

end PlanarHom.MagnitudeSign
