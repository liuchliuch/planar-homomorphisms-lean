import PlanarHom.PositiveWeightRealAvailability
import PlanarHom.DomainWeightedRationalClosure

/-! Source-facing clauses of Lemma3.7 with literal real weights, original
availability and exact prescribed-domain policies. The selected ambient matrix
is already global in the source policy; old vertex domains may be narrower. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases PositiveWeightRemoval PrescribedDomains
variable {q bt ut dt : ℕ} (L : RealLanguage q bt ut)

def rationalWeightProblem (hw : ∀i,0<L.weights i) (r : ℚ) : PromiseProblem :=
  evaluationProblem (powerBasis L.weightsK hw r) (powerMatrices L.matricesK L.weightsK r)
    (powerUnaries L.unariesK L.weightsK r)
    (fun i=>sourceInclusion L.field (powerAlphabet L.weightsK r) (L.weightsK i))

def domainInverseWeightProblem (D : Fin dt→Set (Fin q))
    (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop) (old : Fin bt) : PromiseProblem :=
  domainEvaluationProblem L.basis
    (appendOne L.matricesK (Matrix.diagonal (fun i=>(L.weightsK i)⁻¹))) L.unariesK L.weightsK
    D (appendOne B (B old)) T

def domainUnitWeightProblem (D : Fin dt→Set (Fin q))
    (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop) : PromiseProblem :=
  domainEvaluationProblem L.basis L.matricesK L.unariesK (fun _=>1) D B T

def domainRationalWeightProblem (hw : ∀i,0<L.weights i) (r : ℚ)
    (D : Fin dt→Set (Fin q)) (B : Fin bt→Fin dt→Fin dt→Prop)
    (T : Fin ut→Fin dt→Prop) (old : Fin bt) : PromiseProblem :=
  domainEvaluationProblem (powerBasis L.weightsK hw r) (powerMatrices L.matricesK L.weightsK r)
    (powerUnaries L.unariesK L.weightsK r)
    (fun i=>sourceInclusion L.field (powerAlphabet L.weightsK r) (L.weightsK i))
    D (appendOne B (B old)) (appendOne T (fun _=>True))

/-- Every fixed rational exponent, including0 and negatives; both the binary
D^r and its unary coexist with all old constraints and the original background. -/
def lemma37_rational (old : Fin bt)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hw : ∀i,0<L.weights i) (hnonzero : ∀i,L.matrices old i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (r : ℚ) (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction (L.rationalWeightProblem hw r) base :=
  (rationalDiagonalUnaryReduction L.basis L.matricesK L.unariesK L.weightsK old hs hw hnonzero hproj r).trans available

/-- Narrow original domains are preserved. The global selected-matrix policy
is explicitly present in the supplied original source availability. -/
def lemma37_global_domain_inverse (D : Fin dt→Set (Fin q))
    (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : D full=Set.univ)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hw : ∀i,0<L.weights i) (hnonzero : ∀i,L.matrices old i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (L.domainProblem D (withGlobalMatrix B old) T) base) :
    PromisePolyTimeTuringReduction (L.domainInverseWeightProblem D (withGlobalMatrix B old) T old) base :=
  (domainInverseDiagonalFromRows L.basis L.matricesK L.unariesK L.weightsK D
    (withGlobalMatrix B old) T old full hfull (withGlobalMatrix_self B old) hs hw hnonzero hproj).trans available

/-- The source finite-language implication with the same old domain assignment,
including isolated vertices and all original explicit unary occurrences. -/
def lemma37_global_domain_removeWeights (D : Fin dt→Set (Fin q))
    (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : D full=Set.univ)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hw : ∀i,0<L.weights i) (hnonzero : ∀i,L.matrices old i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (L.domainProblem D (withGlobalMatrix B old) T) base) :
    PromisePolyTimeTuringReduction (L.domainUnitWeightProblem D (withGlobalMatrix B old) T) base :=
  (domainRemovePositiveWeights L.basis L.matricesK L.unariesK L.weightsK D
    (withGlobalMatrix B old) T old full hfull (withGlobalMatrix_self B old) hs hw hnonzero hproj).trans available

/-- The appended unary is allowed exactly because its diagonal loop is already
admissible on every old domain; reserved indicator offsets are compiled. -/
def lemma37_global_domain_rational (D : Fin dt→Set (Fin q))
    (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : D full=Set.univ)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hw : ∀i,0<L.weights i) (hnonzero : ∀i,L.matrices old i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (r : ℚ) (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (L.domainProblem D (withGlobalMatrix B old) T) base) :
    PromisePolyTimeTuringReduction (L.domainRationalWeightProblem hw r D (withGlobalMatrix B old) T old) base :=
  (domainRationalDiagonalUnaryReduction L.basis L.matricesK L.unariesK L.weightsK D
    (withGlobalMatrix B old) T old full hfull (withGlobalMatrix_self B old) hs hw hnonzero hproj r).trans available

/-- Literal real target identities, without changing source weights. -/
theorem rationalWeight_targets (r : ℚ) :
    (∀i j,(powerMatrices L.matricesK L.weightsK r (Fin.last bt) i j : ℝ)=
      Matrix.diagonal (fun i=>L.weights i^(r:ℝ)) i j) ∧
    (∀i,(powerUnaries L.unariesK L.weightsK r (Fin.last ut) i : ℝ)=L.weights i^(r:ℝ)) := by
  constructor
  · intro i j
    rw [powerMatrix_real]
    rfl
  · intro i
    exact powerUnary_real L.unariesK L.weightsK r i

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
