import PlanarHom.AlgebraicProductOverfield

/-! # Real-algebraic joint product interpolation (Lemma 3.1)

This module gives actual raw-bit polynomial-time oracle reductions for a fixed
real-algebraic mixed language, with an appended constraint that coexists with
all source labels. The source presentation is chosen from the original language
alone. The target field is a fixed finite extension, and answer conversion to
that extension is performed by ordinary machines. No field-operation oracle,
computable product map, canonical-input restriction, embedding, or pinning
hypothesis is added. Signed companions and weights are permitted, so positive
background weights and symmetric matrices are covered as special cases.
-/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation
open Complexity Complexity.MixedCode FixedAlgebraicField AlgebraicMixedLanguage
open FiniteLanguageAliases ProductCompatibility

/-- Fixed real-algebraic source data. The number of occurrences is not bounded. -/
structure RealLanguage (q bt ut : ℕ) where
  matrices : Fin bt → Matrix (Fin q) (Fin q) ℝ
  unaries : Fin ut → Fin q → ℝ
  weights : Fin q → ℝ
  matrices_algebraic : ∀ l i j, IsAlgebraic ℚ (matrices l i j)
  unaries_algebraic : ∀ l i, IsAlgebraic ℚ (unaries l i)
  weights_algebraic : ∀ i, IsAlgebraic ℚ (weights i)

namespace RealLanguage
variable {q bt ut dt : ℕ} (L : RealLanguage q bt ut)

def sourceAlphabet := alphabet L.matrices L.unaries L.weights (fun i : Fin 0 => Fin.elim0 i)
def field : IntermediateField ℚ ℝ := commonField L.sourceAlphabet

theorem sourceAlphabet_algebraic : ∀ i, IsAlgebraic ℚ (L.sourceAlphabet i) :=
  alphabet_isAlgebraic _ _ _ _ L.matrices_algebraic L.unaries_algebraic L.weights_algebraic
    (fun i => Fin.elim0 i)

instance fieldFiniteDimensional : FiniteDimensional ℚ L.field :=
  commonField_finiteDimensional _ L.sourceAlphabet_algebraic

def basis : Module.Basis (Fin (Module.finrank ℚ L.field)) ℚ L.field :=
  commonBasis _ L.sourceAlphabet_algebraic

def matricesK (l : Fin bt) (i j : Fin q) : L.field :=
  liftAlphabet L.sourceAlphabet (.inl (l,i,j))
def unariesK (l : Fin ut) (i : Fin q) : L.field :=
  liftAlphabet L.sourceAlphabet (.inr (.inl (l,i)))
def weightsK (i : Fin q) : L.field :=
  liftAlphabet L.sourceAlphabet (.inr (.inr (.inl i)))

@[simp] theorem matricesK_coe (l : Fin bt) (i j : Fin q) :
    (L.matricesK l i j : ℝ) = L.matrices l i j := rfl
@[simp] theorem unariesK_coe (l : Fin ut) (i : Fin q) :
    (L.unariesK l i : ℝ) = L.unaries l i := rfl
@[simp] theorem weightsK_coe (i : Fin q) : (L.weightsK i : ℝ) = L.weights i := rfl

/-- The oracle's exact canonical field answers represent the original real sum. -/
theorem evaluate_coe (g : MixedCode) (hg : g.Valid bt ut) :
    L.field.val (g.evaluate hg L.matricesK L.unariesK L.weightsK) =
      g.evaluate hg L.matrices L.unaries L.weights :=
  map_evaluate L.field.val.toRingHom g hg _ _ _

/-- Intrinsic domains remain the very same subsets of the original color set. -/
theorem evaluateRestricted_coe (g : MixedCode) (hg : g.Valid bt ut)
    (D : Fin dt → Set (Fin q)) (δ : Fin g.vertices → Fin dt) :
    L.field.val (PrescribedDomains.evaluateRestricted g hg L.matricesK L.unariesK L.weightsK D δ) =
      PrescribedDomains.evaluateRestricted g hg L.matrices L.unaries L.weights D δ :=
  PrescribedDomains.map_evaluateRestricted L.field.val.toRingHom g hg _ _ _ D δ

def problem : PromiseProblem := evaluationProblem L.basis L.matricesK L.unariesK L.weightsK

def domainProblem (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) : PromiseProblem :=
  domainEvaluationProblem L.basis L.matricesK L.unariesK L.weightsK D B T

def binaryTargetProblem (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀ i j, IsAlgebraic ℚ (N i j)) :
    PromiseProblem :=
  let A := fun p : Fin q × Fin q => N p.1 p.2
  let φ := sourceInclusion L.field A
  evaluationProblem (extensionBasis L.field A (fun p => hN p.1 p.2))
    (appendOne (fun l i j => φ (L.matricesK l i j)) (fun i j => targetValue L.field A (i,j)))
    (fun l i => φ (L.unariesK l i)) (fun i => φ (L.weightsK i))

def unaryTargetProblem (N : Fin q → ℝ) (hN : ∀ i, IsAlgebraic ℚ (N i)) : PromiseProblem :=
  let φ := sourceInclusion L.field N
  evaluationProblem (extensionBasis L.field N hN) (fun l i j => φ (L.matricesK l i j))
    (appendOne (fun l i => φ (L.unariesK l i)) (targetValue L.field N)) (fun i => φ (L.weightsK i))

def domainBinaryTargetProblem (D : Fin dt → Set (Fin q))
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀ i j, IsAlgebraic ℚ (N i j)) (old : Fin bt) :
    PromiseProblem :=
  let A := fun p : Fin q × Fin q => N p.1 p.2
  let φ := sourceInclusion L.field A
  domainEvaluationProblem (extensionBasis L.field A (fun p => hN p.1 p.2))
    (appendOne (fun l i j => φ (L.matricesK l i j)) (fun i j => targetValue L.field A (i,j)))
    (fun l i => φ (L.unariesK l i)) (fun i => φ (L.weightsK i)) D (appendOne B (B old)) T

def domainUnaryTargetProblem (D : Fin dt → Set (Fin q))
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (N : Fin q → ℝ) (hN : ∀ i, IsAlgebraic ℚ (N i)) (old : Fin ut) : PromiseProblem :=
  let φ := sourceInclusion L.field N
  domainEvaluationProblem (extensionBasis L.field N hN) (fun l i j => φ (L.matricesK l i j))
    (appendOne (fun l i => φ (L.unariesK l i)) (targetValue L.field N)) (fun i => φ (L.weightsK i))
    D B (appendOne T (T old))

/-- The appended binary language is exactly the stated real language. -/
theorem binaryTarget_evaluate_coe (N : Matrix (Fin q) (Fin q) ℝ)
    (g : MixedCode) (hg : g.Valid (bt+1) ut) :
    let A := fun p : Fin q × Fin q => N p.1 p.2
    let φ := sourceInclusion L.field A
    (extensionField L.field A).val (g.evaluate hg
      (appendOne (fun l i j => φ (L.matricesK l i j)) (fun i j => targetValue L.field A (i,j)))
      (fun l i => φ (L.unariesK l i)) (fun i => φ (L.weightsK i))) =
      g.evaluate hg (appendOne L.matrices N) L.unaries L.weights := by
  dsimp only
  let A := fun p : Fin q × Fin q => N p.1 p.2
  let φ := sourceInclusion L.field A
  have hm : (fun l i j => ((appendOne (fun l i j => φ (L.matricesK l i j))
      (fun i j => targetValue L.field A (i,j)) l i j) : ℝ)) = appendOne L.matrices N := by
    funext l
    refine Fin.addCases (fun k => ?_) (fun k => ?_) l
    · rw [appendOne_old, appendOne_old]
      rfl
    · simp only [appendOne, Fin.addCases_right]
      rfl
  have h := map_evaluate (extensionField L.field A).val.toRingHom g hg
      (appendOne (fun l i j => φ (L.matricesK l i j)) (fun i j => targetValue L.field A (i,j)))
      (fun l i => φ (L.unariesK l i)) (fun i => φ (L.weightsK i))
  change _ = g.evaluate hg (fun l i j => ((appendOne (fun l i j => φ (L.matricesK l i j))
    (fun i j => targetValue L.field A (i,j)) l i j) : ℝ)) L.unaries L.weights at h
  rw [hm] at h
  exact h

/-- Every source unary remains present beside the literal real target unary. -/
theorem unaryTarget_evaluate_coe (N : Fin q → ℝ) (g : MixedCode) (hg : g.Valid bt (ut+1)) :
    let φ := sourceInclusion L.field N
    (extensionField L.field N).val (g.evaluate hg (fun l i j => φ (L.matricesK l i j))
      (appendOne (fun l i => φ (L.unariesK l i)) (targetValue L.field N))
      (fun i => φ (L.weightsK i))) =
      g.evaluate hg L.matrices (appendOne L.unaries N) L.weights := by
  dsimp only
  let φ := sourceInclusion L.field N
  have hu : (fun l i => ((appendOne (fun l i => φ (L.unariesK l i))
      (targetValue L.field N) l i) : ℝ)) = appendOne L.unaries N := by
    funext l
    refine Fin.addCases (fun k => ?_) (fun k => ?_) l
    · rw [appendOne_old, appendOne_old]
      rfl
    · simp only [appendOne, Fin.addCases_right]
      rfl
  have h := map_evaluate (extensionField L.field N).val.toRingHom g hg
      (fun l i j => φ (L.matricesK l i j))
      (appendOne (fun l i => φ (L.unariesK l i)) (targetValue L.field N)) (fun i => φ (L.weightsK i))
  change _ = g.evaluate hg L.matrices (fun l i => ((appendOne (fun l i => φ (L.unariesK l i))
    (targetValue L.field N) l i) : ℝ)) L.weights at h
  rw [hu] at h
  exact h

/-- Exact real restricted-assignment semantics of the appended binary problem. -/
theorem binaryTarget_evaluateRestricted_coe (N : Matrix (Fin q) (Fin q) ℝ)
    (g : MixedCode) (hg : g.Valid (bt+1) ut)
    (D : Fin dt → Set (Fin q)) (δ : Fin g.vertices → Fin dt) :
    let A := fun p : Fin q × Fin q => N p.1 p.2
    let φ := sourceInclusion L.field A
    (extensionField L.field A).val (PrescribedDomains.evaluateRestricted g hg
      (appendOne (fun l i j => φ (L.matricesK l i j)) (fun i j => targetValue L.field A (i,j)))
      (fun l i => φ (L.unariesK l i)) (fun i => φ (L.weightsK i)) D δ) =
      PrescribedDomains.evaluateRestricted g hg (appendOne L.matrices N) L.unaries L.weights D δ := by
  dsimp only
  let A := fun p : Fin q × Fin q => N p.1 p.2
  let φ := sourceInclusion L.field A
  have hm : (fun l i j => ((appendOne (fun l i j => φ (L.matricesK l i j))
      (fun i j => targetValue L.field A (i,j)) l i j) : ℝ)) = appendOne L.matrices N := by
    funext l
    refine Fin.addCases (fun k => ?_) (fun k => ?_) l
    · rw [appendOne_old, appendOne_old]
      rfl
    · simp only [appendOne, Fin.addCases_right]
      rfl
  have h := PrescribedDomains.map_evaluateRestricted (extensionField L.field A).val.toRingHom g hg
      (appendOne (fun l i j => φ (L.matricesK l i j)) (fun i j => targetValue L.field A (i,j)))
      (fun l i => φ (L.unariesK l i)) (fun i => φ (L.weightsK i)) D δ
  change _ = PrescribedDomains.evaluateRestricted g hg (fun l i j => ((appendOne (fun l i j => φ (L.matricesK l i j))
    (fun i j => targetValue L.field A (i,j)) l i j) : ℝ)) L.unaries L.weights D δ at h
  rw [hm] at h
  exact h

/-- Exact real restricted-assignment semantics of the appended unary problem. -/
theorem unaryTarget_evaluateRestricted_coe (N : Fin q → ℝ) (g : MixedCode) (hg : g.Valid bt (ut+1))
    (D : Fin dt → Set (Fin q)) (δ : Fin g.vertices → Fin dt) :
    let φ := sourceInclusion L.field N
    (extensionField L.field N).val (PrescribedDomains.evaluateRestricted g hg (fun l i j => φ (L.matricesK l i j))
      (appendOne (fun l i => φ (L.unariesK l i)) (targetValue L.field N))
      (fun i => φ (L.weightsK i)) D δ) =
      PrescribedDomains.evaluateRestricted g hg L.matrices (appendOne L.unaries N) L.weights D δ := by
  dsimp only
  let φ := sourceInclusion L.field N
  have hu : (fun l i => ((appendOne (fun l i => φ (L.unariesK l i))
      (targetValue L.field N) l i) : ℝ)) = appendOne L.unaries N := by
    funext l
    refine Fin.addCases (fun k => ?_) (fun k => ?_) l
    · rw [appendOne_old, appendOne_old]
      rfl
    · simp only [appendOne, Fin.addCases_right]
      rfl
  have h := PrescribedDomains.map_evaluateRestricted (extensionField L.field N).val.toRingHom g hg
      (fun l i j => φ (L.matricesK l i j))
      (appendOne (fun l i => φ (L.unariesK l i)) (targetValue L.field N)) (fun i => φ (L.weightsK i)) D δ
  change _ = PrescribedDomains.evaluateRestricted g hg L.matrices (fun l i => ((appendOne (fun l i => φ (L.unariesK l i))
    (targetValue L.field N) l i) : ℝ)) L.weights D δ at h
  rw [hu] at h
  exact h

/-- Binary joint product interpolation for actual real-algebraic matrices.
The supplied availability may target any fixed base promise problem. -/
def lemma31_binary (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀ i j, IsAlgebraic ℚ (N i j))
    (old : Fin bt) (hzero : ∀ i j, L.matrices old i j = 0 → N i j = 0)
    (hproducts : HasProductMaps (fun p : Fin q × Fin q => L.matrices old p.1 p.2) (fun p => N p.1 p.2))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction (L.binaryTargetProblem N hN) base :=
  (binaryOverfieldReduction L.basis L.matricesK L.unariesK L.weightsK N hN old hzero hproducts).trans available

/-- The unary assertion of Lemma 3.1, with all old unary labels retained. -/
def lemma31_unary (N : Fin q → ℝ) (hN : ∀ i, IsAlgebraic ℚ (N i))
    (old : Fin ut) (hzero : ∀ i, L.unaries old i = 0 → N i = 0)
    (hproducts : HasProductMaps (L.unaries old) N)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction (L.unaryTargetProblem N hN) base :=
  (unaryOverfieldReduction L.basis L.matricesK L.unariesK L.weightsK N hN old hzero hproducts).trans available

/-- Source-faithful binary joint availability with original prescribed domains,
ordered endpoint typing, and unrestricted ordinary planar raw inputs. -/
def lemma31_domain_binary (D : Fin dt → Set (Fin q))
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀ i j, IsAlgebraic ℚ (N i j)) (old : Fin bt)
    (hzero : ∀ i j, L.matrices old i j = 0 → N i j = 0)
    (hproducts : HasProductMaps (fun p : Fin q × Fin q => L.matrices old p.1 p.2) (fun p => N p.1 p.2))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction (L.domainBinaryTargetProblem D B T N hN old) base :=
  (domainBinaryOverfieldReduction L.basis L.matricesK L.unariesK L.weightsK D B T N hN old hzero hproducts).trans available

/-- Source-faithful unary joint availability, including actual reserved-offset
relabeling rather than a new freely usable indicator language. -/
def lemma31_domain_unary (D : Fin dt → Set (Fin q))
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (N : Fin q → ℝ) (hN : ∀ i, IsAlgebraic ℚ (N i)) (old : Fin ut)
    (hzero : ∀ i, L.unaries old i = 0 → N i = 0) (hproducts : HasProductMaps (L.unaries old) N)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction (L.domainUnaryTargetProblem D B T N hN old) base :=
  (domainUnaryOverfieldReduction L.basis L.matricesK L.unariesK L.weightsK D B T N hN old hzero hproducts).trans available

end RealLanguage
end PlanarHom.AlgebraicProductInterpolation
