import PlanarHom.FiniteLanguageJointReductions
import PlanarHom.OracleReductionLaws

/-! Actual homogeneous/finitely mixed consequences of joint interpolation.
All constraints retain their original field output representation and backgrounds. -/
noncomputable section
namespace PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLanguageAliases PlanarHom.ProductCompatibility
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {q dimension u r d : ℕ}

def evaluationRefl (basis : Module.Basis (Fin dimension) ℚ K)
    {b : ℕ} (M : Fin b → Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M U w) (evaluationProblem basis M U w) :=
  let bound := evaluationProblem_output_bound basis M U w
  .refl_of_output_bound _ (Classical.choose bound) (Classical.choose_spec bound)

def domainEvaluationRefl (basis : Module.Basis (Fin dimension) ℚ K)
    {b : ℕ} (M : Fin b → Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K)
    (D : Fin d → Set (Fin q)) (B : Fin b → Fin d → Fin d → Prop) (T : Fin u → Fin d → Prop) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U w D B T)
      (domainEvaluationProblem basis M U w D B T) :=
  let bound := domainEvaluationProblem_output_bound basis M U w D B T
  .refl_of_output_bound _ (Classical.choose bound) (Classical.choose_spec bound)

def homogeneousProductReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M N : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K)
    (hzero : ∀ i j, M i j = 0 → N i j = 0)
    (hmaps : HasProductMaps (fun p : Fin q × Fin q => M p.1 p.2) (fun p => N p.1 p.2)) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (fun _ : Fin 1 => N) U w)
      (evaluationProblem basis (fun _ : Fin 1 => M) U w) :=
  binaryProductReduction basis (fun _ => M) (fun _ => N) U w 0
    (by intro l hl; have he : l = 0 := Subsingleton.elim _ _; subst l; exact (hl rfl).elim)
    hzero hmaps

def domainHomogeneousProductReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M N : Matrix (Fin q) (Fin q) K) (U : Fin u → Fin q → K) (w : Fin q → K)
    (D : Fin d → Set (Fin q)) (E : Fin d → Fin d → Prop) (T : Fin u → Fin d → Prop)
    (hzero : ∀ i j, M i j = 0 → N i j = 0)
    (hmaps : HasProductMaps (fun p : Fin q × Fin q => M p.1 p.2) (fun p => N p.1 p.2)) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis (fun _ : Fin 1 => N) U w D (fun _ => E) T)
      (domainEvaluationProblem basis (fun _ : Fin 1 => M) U w D (fun _ => E) T) :=
  domainBinaryProductReduction basis (fun _ => M) (fun _ => N) U w D (fun _ => E) T 0
    (by intro l hl; have he : l = 0 := Subsingleton.elim _ _; subst l; exact (hl rfl).elim)
    hzero hmaps

/-- A real finite-label alias removes the retained original slot only from the
requested target input; the available mixed oracle still retains every old type. -/
def finiteProductReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (N : Fin r → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K)
    (hzero : ∀ l i j, M i j = 0 → N l i j = 0)
    (hmaps : ∀ l, HasProductMaps (fun p : Fin q × Fin q => M p.1 p.2) (fun p => N l p.1 p.2)) :
    PromisePolyTimeTuringReduction (evaluationProblem basis N U w)
      (evaluationProblem basis (fun _ : Fin 1 => M) U w) := by
  let old : Fin 1 → Matrix (Fin q) (Fin q) K := fun _ => M
  let r1 := binaryFiniteProduct_joint basis old U w N (fun _ => 0) hzero hmaps
    (evaluationProblem basis old U w) (evaluationRefl basis old U w)
  let r2 := binaryRelabelReduction basis (Fin.natAdd 1) (appendFamily old N) U w
  have he : appendFamily old N ∘ Fin.natAdd 1 = N := by
    funext i
    exact appendFamily_new old N i
  simpa only [he] using r2.trans r1

def domainFiniteProductReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix (Fin q) (Fin q) K) (N : Fin r → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K)
    (D : Fin d → Set (Fin q)) (E : Fin d → Fin d → Prop) (T : Fin u → Fin d → Prop)
    (hzero : ∀ l i j, M i j = 0 → N l i j = 0)
    (hmaps : ∀ l, HasProductMaps (fun p : Fin q × Fin q => M p.1 p.2) (fun p => N l p.1 p.2)) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis N U w D (fun _ => E) T)
      (domainEvaluationProblem basis (fun _ : Fin 1 => M) U w D (fun _ => E) T) := by
  let old : Fin 1 → Matrix (Fin q) (Fin q) K := fun _ => M
  let oldB : Fin 1 → Fin d → Fin d → Prop := fun _ => E
  let newB : Fin r → Fin d → Fin d → Prop := fun _ => E
  let r1 := domainBinaryFiniteProduct_joint basis old U w D oldB T N newB (fun _ => 0)
    (fun _ _ _ h => h) hzero hmaps (domainEvaluationProblem basis old U w D oldB T)
    (domainEvaluationRefl basis old U w D oldB T)
  let r2 := domainBinaryRelabelReduction basis (Fin.natAdd 1) (appendFamily old N) U w D
    newB (appendFamily oldB newB) T (by intro i x y h; simpa only [appendFamily_new] using h)
  have he : appendFamily old N ∘ Fin.natAdd 1 = N := by
    funext i
    exact appendFamily_new old N i
  simpa only [he] using r2.trans r1

end PlanarHom.Complexity.MixedCode
