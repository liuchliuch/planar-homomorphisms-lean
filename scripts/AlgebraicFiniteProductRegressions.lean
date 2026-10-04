import PlanarHom.AlgebraicFiniteProductInterpolation
import PlanarHom.OracleReductionLaws
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open AlgebraicProductInterpolation ProductCompatibility
noncomputable section

def language : RealLanguage 2 1 2 where
  matrices := fun _ _ _ => 2
  unaries := fun l _ => if l.val = 0 then 2 else -5
  weights := fun _ => 1
  matrices_algebraic := by
    intro _ _ _
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (2 : ℚ)
  unaries_algebraic := by
    intro l _
    split
    · simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (2 : ℚ)
    · simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (-5 : ℚ)
  weights_algebraic := by
    intro _
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (1 : ℚ)

theorem target_algebraic : IsAlgebraic ℚ (3 : ℝ) := by
  simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (3 : ℚ)

def sourceAvailable : PromisePolyTimeTuringReduction language.problem language.problem := by
  let bound := evaluationProblem_output_bound language.basis language.matricesK language.unariesK language.weightsK
  exact .refl_of_output_bound _ (Classical.choose bound) (Classical.choose_spec bound)

theorem constant_products {I : Type} : HasProductMaps (fun _ : I => (2 : ℝ)) (fun _ => (3 : ℝ)) := by
  apply hasProductMaps_of_compatible
  intro xs ys hlen _ _ _
  simp [hlen]

def binaryReduction := language.lemma31_binary (fun _ _ => 3) (fun _ _ => target_algebraic) 0
  (by intro i j h; norm_num [language] at h) constant_products _ sourceAvailable

def unaryReduction := language.lemma31_unary (fun _ => 3) (fun _ => target_algebraic) 0
  (by intro i h; norm_num [language] at h) constant_products _ sourceAvailable

def domains : Fin 1 → Set (Fin 2) := fun _ => {0}
def binaryTyping : Fin 1 → Fin 1 → Fin 1 → Prop := fun _ _ _ => True
def unaryTyping : Fin 2 → Fin 1 → Prop := fun _ _ => True

def domainAvailable : PromisePolyTimeTuringReduction
    (language.domainProblem domains binaryTyping unaryTyping)
    (language.domainProblem domains binaryTyping unaryTyping) := by
  let bound := domainEvaluationProblem_output_bound language.basis language.matricesK language.unariesK
    language.weightsK domains binaryTyping unaryTyping
  exact .refl_of_output_bound _ (Classical.choose bound) (Classical.choose_spec bound)

def domainBinaryReduction := language.lemma31_domain_binary domains binaryTyping unaryTyping
  (fun _ _ => 3) (fun _ _ => target_algebraic) 0
  (by intro i j h; norm_num [language] at h) constant_products _ domainAvailable

def domainUnaryReduction := language.lemma31_domain_unary domains binaryTyping unaryTyping
  (fun _ => 3) (fun _ => target_algebraic) 0
  (by intro i h; norm_num [language] at h) constant_products _ domainAvailable

-- The original source field is fixed before any target is specified.
example (l : Fin 2) (i : Fin 2) : (language.unariesK l i : ℝ) =
    (if l.val = 0 then 2 else -5) := rfl
-- Coexisting old and auxiliary labels preserve the old slot exactly.
example : FiniteLanguageAliases.appendOne language.unaries (fun _ => (3 : ℝ))
    (Fin.castAdd 1 (0 : Fin 2)) (0 : Fin 2) = 2 := by
  rw [FiniteLanguageAliases.appendOne_old]
  rfl
example : FiniteLanguageAliases.appendOne language.unaries (fun _ => (3 : ℝ))
    (Fin.last 2) (0 : Fin 2) = 3 := by rw [FiniteLanguageAliases.appendOne_aux]
#print axioms binaryReduction
#print axioms unaryReduction
#print axioms domainBinaryReduction
#print axioms domainUnaryReduction

-- Two binary and two unary targets coexist in ONE extension field.
def finiteReduction := language.lemma31_mixedFinite
  (fun _ : Fin 2 => fun _ _ => (3 : ℝ)) (fun _ : Fin 2 => fun _ => (3 : ℝ))
  (fun _ _ _ => target_algebraic) (fun _ _ => target_algebraic)
  (fun _ => 0) (fun _ => 0)
  (by intro l i j h; norm_num [language] at h) (fun _ => constant_products)
  (by intro l i h; norm_num [language] at h) (fun _ => constant_products) _ sourceAvailable

def domainFiniteReduction := language.lemma31_domain_mixedFinite domains binaryTyping unaryTyping
  (fun _ : Fin 2 => fun _ _ => (3 : ℝ)) (fun _ : Fin 2 => fun _ => (3 : ℝ))
  (fun _ _ _ => target_algebraic) (fun _ _ => target_algebraic)
  (fun _ => 0) (fun _ => 0)
  (by intro l i j h; norm_num [language] at h) (fun _ => constant_products)
  (by intro l i h; norm_num [language] at h) (fun _ => constant_products) _ domainAvailable

-- Empty auxiliary languages are also accepted, without a nonempty-family premise.
def emptyFiniteReduction := language.lemma31_mixedFinite
  (fun l : Fin 0 => Fin.elim0 l) (fun l : Fin 0 => Fin.elim0 l)
  (fun l => Fin.elim0 l) (fun l => Fin.elim0 l)
  (fun l => Fin.elim0 l) (fun l => Fin.elim0 l)
  (fun l => Fin.elim0 l) (fun l => Fin.elim0 l)
  (fun l => Fin.elim0 l) (fun l => Fin.elim0 l) _ sourceAvailable
#print axioms finiteReduction
#print axioms domainFiniteReduction
#print axioms emptyFiniteReduction
