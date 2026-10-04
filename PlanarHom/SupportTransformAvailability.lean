import PlanarHom.AlgebraicFiniteProductInterpolation
import PlanarHom.SupportTransformCompatibility

/-! The joint support/magnitude/sign clause of Corollary 3.2, using actual
Lemma 3.1 machines and retaining all original mixed-language companions. -/
noncomputable section
namespace PlanarHom.SupportTransformAvailability
open Complexity Complexity.MixedCode ProductCompatibility AlgebraicProductInterpolation
variable {q bt ut : ℕ}

def triad (M : Matrix (Fin q) (Fin q) ℝ) : Fin 3 → Matrix (Fin q) (Fin q) ℝ :=
  ![fun i j => supportTransform (fun p : Fin q × Fin q => M p.1 p.2) (i,j),
    fun i j => |M i j|, fun i j => Real.sign (M i j)]

theorem triad_algebraic (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : ∀ i j, IsAlgebraic ℚ (M i j)) : ∀ l i j, IsAlgebraic ℚ (triad M l i j) := by
  intro l i j
  fin_cases l
  · exact supportTransform_isAlgebraic _ _
  · exact abs_isAlgebraic (hM i j)
  · exact sign_isAlgebraic _

theorem triad_zero (M : Matrix (Fin q) (Fin q) ℝ) :
    ∀ l i j, M i j = 0 → triad M l i j = 0 := by
  intro l i j h
  fin_cases l
  · exact supportTransform_zero _ h
  · change |M i j| = 0
    rw [h, abs_zero]
  · change Real.sign (M i j) = 0
    rw [h, Real.sign_zero]

theorem triad_products (M : Matrix (Fin q) (Fin q) ℝ) :
    ∀ l, HasProductMaps (fun p : Fin q × Fin q => M p.1 p.2)
      (fun p => triad M l p.1 p.2) := by
  intro l
  fin_cases l
  · exact hasProductMaps_support _
  · exact hasProductMaps_abs _
  · exact hasProductMaps_sign _

def supportMagnitudeSign_joint (L : RealLanguage q bt ut) (old : Fin bt)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :=
  L.lemma31_mixedFinite (triad (L.matrices old)) (fun i : Fin 0 => Fin.elim0 i)
    (triad_algebraic _ (L.matrices_algebraic old)) (fun i => Fin.elim0 i)
    (fun _ => old) (fun i => Fin.elim0 i) (triad_zero _) (triad_products _)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) base available

def supportMagnitudeSign_domain_joint {dt : ℕ} (L : RealLanguage q bt ut) (old : Fin bt)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :=
  L.lemma31_domain_mixedFinite D B T (triad (L.matrices old)) (fun i : Fin 0 => Fin.elim0 i)
    (triad_algebraic _ (L.matrices_algebraic old)) (fun i => Fin.elim0 i)
    (fun _ => old) (fun i => Fin.elim0 i) (triad_zero _) (triad_products _)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) base available

end PlanarHom.SupportTransformAvailability
