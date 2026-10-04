import PlanarHom.BooleanNormalizedFamilyIdentification
import PlanarHom.DomainEndpointLoopParameterAvailability
import PlanarHom.AlgebraicProductOverfield
import PlanarHom.SpectralRealAvailability

/-! Source-facing uniform equation5.2 availability in one fixed extension for
the normalization scalar, with actual conversion to the original source basis. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases BooleanPDNormalization CubeTensorExponential
variable {q b u d : ℕ} (L : RealLanguage q b u)

def booleanConstants (γ : ℝ) : Fin 1→ℝ:=fun _=>γ
abbrev booleanFamilyField (γ : ℝ) := extensionField L.field (booleanConstants γ)
def booleanFamilyBasis (γ : ℝ) (hγalg : IsAlgebraic ℚ γ) :=
  extensionBasis L.field (booleanConstants γ) (fun _=>hγalg)
def booleanFamilyMatrices (γ : ℝ) : Fin b→Matrix (Fin q) (Fin q) (L.booleanFamilyField γ) :=
  fun l i j=>sourceInclusion L.field (booleanConstants γ) (L.matricesK l i j)
def booleanFamilyUnaries (γ : ℝ) : Fin u→Fin q→L.booleanFamilyField γ :=
  fun l i=>sourceInclusion L.field (booleanConstants γ) (L.unariesK l i)
def booleanFamilyScalar (γ : ℝ) : L.booleanFamilyField γ:=targetValue L.field (booleanConstants γ) 0

@[simp] theorem booleanFamilyMatrices_real (γ : ℝ) (old : Fin b) :
    SpectralFieldPresentation.realMatrix (L.booleanFamilyMatrices γ old)=L.matrices old := rfl
@[simp] theorem booleanFamilyScalar_real (γ : ℝ) : (L.booleanFamilyScalar γ : ℝ)=γ := rfl

def booleanFamilyProblem (γ : ℝ) (hγalg : IsAlgebraic ℚ γ) (old : Fin b) (k : ℕ) : PromiseProblem:=
  ParameterizedMatrixEvaluation.problem (L.booleanFamilyBasis γ hγalg) BitEncoding.rat
    (L.booleanFamilyMatrices γ) (L.booleanFamilyUnaries γ) (fun _=>1)
    (EndpointLoopParameterAvailability.family (L.booleanFamilyMatrices γ old) k
      (((L.booleanFamilyScalar γ)^(2*k+1))⁻¹)) (fun x : ℚ=>0<x)

def booleanFamilyReduction (hunit : ∀i,L.weights i=1) (old : Fin b)
    (e : Fin q≃Boolean.Cube d) (γ : ℝ) (hγ : 0<γ) (hγalg : IsAlgebraic ℚ γ)
    (θ w : Fin d→ℝ) (hθ : ∀r,0<θ r) (hw : ∀r,0<w r) (hw1 : ∀r,w r<1)
    (hsource : Matrix.reindex e e (L.matrices old)=γ • tensor (fun r=>normalForm (θ r) (w r)))
    (k : ℕ) (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction (L.booleanFamilyProblem γ hγalg old k) base := by
  letI:=extension_finiteDimensional L.field (booleanConstants γ) (fun _=>hγalg)
  let A:=L.booleanFamilyMatrices γ old
  let c:=L.booleanFamilyScalar γ
  have hs : Matrix.reindex e e (SpectralFieldPresentation.realMatrix A)=
      (c : ℝ) • tensor (fun r=>normalForm (θ r) (w r)):=hsource
  have hp:=BooleanNormalizedFamilyIdentification.source_posDef A e c hγ θ w hθ hw hw1 hs
  have hconn:=(BooleanNormalizedFamilyIdentification.sourceGraphIso A e c hγ θ w hθ hw hw1 hs).connected_iff.mpr
    (Boolean.cubeGraph_connected d)
  have hpos:=BooleanNormalizedFamilyIdentification.source_positive_log A e c hγ θ w hθ hw hw1 hs
  have source : PromisePolyTimeTuringReduction
      (evaluationProblem (L.booleanFamilyBasis γ hγalg) (L.booleanFamilyMatrices γ)
        (L.booleanFamilyUnaries γ) (fun _=>1)) base := by
    let r:=fieldMapReduction L.basis (L.booleanFamilyBasis γ hγalg)
      (sourceInclusion L.field (booleanConstants γ)) L.matricesK L.unariesK (fun _=>1)
    have a : PromisePolyTimeTuringReduction (evaluationProblem L.basis L.matricesK L.unariesK (fun _=>1)) base := by
      simpa only [RealLanguage.problem,weightsK_eq_one L hunit] using available
    simpa only [map_one] using r.trans a
  exact EndpointLoopParameterAvailability.reduction (L.booleanFamilyBasis γ hγalg)
    (L.booleanFamilyMatrices γ) (L.booleanFamilyUnaries γ) old k ((c^(2*k+1))⁻¹) hp hconn hpos base source

theorem booleanFamily_matrix_real (old : Fin b) (e : Fin q≃Boolean.Cube d)
    (γ : ℝ) (hγ : 0<γ) (hγalg : IsAlgebraic ℚ γ)
    (θ w : Fin d→ℝ) (hθ : ∀r,0<θ r) (hw : ∀r,0<w r) (hw1 : ∀r,w r<1)
    (hsource : Matrix.reindex e e (L.matrices old)=γ • tensor (fun r=>normalForm (θ r) (w r)))
    (k : ℕ) (x : ℚ) :
    Matrix.reindex e e (SpectralFieldPresentation.realMatrix
      (EndpointLoopParameterAvailability.family (L.booleanFamilyMatrices γ old) k
        (((L.booleanFamilyScalar γ)^(2*k+1))⁻¹) x))=
      tensor (fun r=>normalForm ((θ r)^(2*k+1)) (w r*(x : ℝ))) := by
  letI:=extension_finiteDimensional L.field (booleanConstants γ) (fun _=>hγalg)
  exact BooleanNormalizedFamilyIdentification.family_real (L.booleanFamilyMatrices γ old) e (L.booleanFamilyScalar γ) hγ θ w hθ hw hw1 hsource k x

def domainBooleanFamilyProblem {dt : ℕ} (γ : ℝ) (hγalg : IsAlgebraic ℚ γ)
    (D : Fin dt→Set (Fin q)) (B : Fin b→Fin dt→Fin dt→Prop) (T : Fin u→Fin dt→Prop)
    (old : Fin b) (k : ℕ) : PromiseProblem:=
  DomainEndpointLoopParameterAvailability.targetProblem (L.booleanFamilyBasis γ hγalg)
    (L.booleanFamilyMatrices γ) (L.booleanFamilyUnaries γ) D
    (PrescribedDomains.withGlobalMatrix B old) T old k (((L.booleanFamilyScalar γ)^(2*k+1))⁻¹)

/-- The source policy already treats the distinguished matrix as global; all
old narrower vertex domains and companion permissions survive every layer. -/
def domainBooleanFamilyReduction {dt : ℕ} (hunit : ∀i,L.weights i=1)
    (D : Fin dt→Set (Fin q)) (B : Fin b→Fin dt→Fin dt→Prop) (T : Fin u→Fin dt→Prop)
    (old : Fin b) (full : Fin dt) (hfull : D full=Set.univ)
    (e : Fin q≃Boolean.Cube d) (γ : ℝ) (hγ : 0<γ) (hγalg : IsAlgebraic ℚ γ)
    (θ w : Fin d→ℝ) (hθ : ∀r,0<θ r) (hw : ∀r,0<w r) (hw1 : ∀r,w r<1)
    (hsource : Matrix.reindex e e (L.matrices old)=γ • tensor (fun r=>normalForm (θ r) (w r)))
    (k : ℕ) (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (L.domainProblem D (PrescribedDomains.withGlobalMatrix B old) T) base) :
    PromisePolyTimeTuringReduction (L.domainBooleanFamilyProblem γ hγalg D B T old k) base := by
  letI:=extension_finiteDimensional L.field (booleanConstants γ) (fun _=>hγalg)
  let A:=L.booleanFamilyMatrices γ old
  let c:=L.booleanFamilyScalar γ
  have hs : Matrix.reindex e e (SpectralFieldPresentation.realMatrix A)=
      (c : ℝ) • tensor (fun r=>normalForm (θ r) (w r)):=hsource
  have hp:=BooleanNormalizedFamilyIdentification.source_posDef A e c hγ θ w hθ hw hw1 hs
  have hconn:=(BooleanNormalizedFamilyIdentification.sourceGraphIso A e c hγ θ w hθ hw hw1 hs).connected_iff.mpr
    (Boolean.cubeGraph_connected d)
  have hpos:=BooleanNormalizedFamilyIdentification.source_positive_log A e c hγ θ w hθ hw hw1 hs
  have source : PromisePolyTimeTuringReduction
      (domainEvaluationProblem (L.booleanFamilyBasis γ hγalg) (L.booleanFamilyMatrices γ)
        (L.booleanFamilyUnaries γ) (fun _=>1) D (PrescribedDomains.withGlobalMatrix B old) T) base := by
    let r:=domainFieldMapReduction L.basis (L.booleanFamilyBasis γ hγalg)
      (sourceInclusion L.field (booleanConstants γ)) L.matricesK L.unariesK (fun _=>1)
      D (PrescribedDomains.withGlobalMatrix B old) T
    have a : PromisePolyTimeTuringReduction
        (domainEvaluationProblem L.basis L.matricesK L.unariesK (fun _=>1) D
          (PrescribedDomains.withGlobalMatrix B old) T) base := by
      simpa only [RealLanguage.domainProblem,weightsK_eq_one L hunit] using available
    simpa only [map_one] using r.trans a
  exact DomainEndpointLoopParameterAvailability.reduction_global (L.booleanFamilyBasis γ hγalg)
    (L.booleanFamilyMatrices γ) (L.booleanFamilyUnaries γ) D B T old k ((c^(2*k+1))⁻¹)
    full hfull hp hconn hpos base source

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
