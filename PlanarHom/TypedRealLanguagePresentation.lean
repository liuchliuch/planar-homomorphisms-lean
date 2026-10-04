import PlanarHom.AlgebraicLanguageExtensions
import PlanarHom.PrescribedDomainAliasReductions

/-! Canonical real-language field/basis bridges with exact original typed raw
promises. Domains and endpoint policies are retained, never replaced by free pins. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases
variable {q bt ut bs us dimension dt : ℕ}

def typedProblem (L : RealLanguage q bt ut) (D : Fin dt→Set (Fin q))
    (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop) : PromiseProblem :=
  domainEvaluationProblem L.basis L.matricesK L.unariesK L.weightsK D B T

def typedPresentationDescentReduction (L : RealLanguage q bt ut)
    (D : Fin dt→Set (Fin q)) (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (K : IntermediateField ℚ ℝ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K)
    (hM : ∀l i j,(M l i j:ℝ)=L.matrices l i j)
    (hU : ∀l i,(U l i:ℝ)=L.unaries l i) (hw : ∀i,(w i:ℝ)=L.weights i) :
    PromisePolyTimeTuringReduction (L.typedProblem D B T)
      (domainEvaluationProblem basis M U w D B T) := by
  let φ := IntermediateField.inclusion (L.field_le_of_realization K M U w hM hU hw)
  have hm : (fun l i j=>φ (L.matricesK l i j))=M := by
    funext l i j
    exact Subtype.ext (hM l i j).symm
  have hu : (fun l i=>φ (L.unariesK l i))=U := by
    funext l i
    exact Subtype.ext (hU l i).symm
  have hwp : (fun i=>φ (L.weightsK i))=w := by
    funext i
    exact Subtype.ext (hw i).symm
  have r := domainFieldDescentReduction L.basis basis φ L.matricesK L.unariesK L.weightsK D B T
  simpa only [hm,hu,hwp] using r

def typedRelabelReduction (target : RealLanguage q bt ut) (source : RealLanguage q bs us)
    (D : Fin dt→Set (Fin q)) (BT : Fin bt→Fin dt→Fin dt→Prop)
    (BS : Fin bs→Fin dt→Fin dt→Prop) (TT : Fin ut→Fin dt→Prop) (TS : Fin us→Fin dt→Prop)
    (rb : Fin bt→Fin bs) (ru : Fin ut→Fin us)
    (hB : ∀l x y,BT l x y→BS (rb l) x y) (hT : ∀l x,TT l x→TS (ru l) x)
    (hM : ∀l i j,target.matrices l i j=source.matrices (rb l) i j)
    (hU : ∀l i,target.unaries l i=source.unaries (ru l) i) (hw : ∀i,target.weights i=source.weights i) :
    PromisePolyTimeTuringReduction (target.typedProblem D BT TT) (source.typedProblem D BS TS) := by
  have present := target.typedPresentationDescentReduction D BT TT source.field source.basis
    (source.matricesK ∘ rb) (source.unariesK ∘ ru) source.weightsK
    (fun l i j=>(hM l i j).symm) (fun l i=>(hU l i).symm) (fun i=>(hw i).symm)
  have binary := domainBinaryRelabelReduction source.basis rb source.matricesK
    (source.unariesK ∘ ru) source.weightsK D BT BS TT hB
  have unary := domainUnaryRelabelReduction source.basis ru source.matricesK source.unariesK
    source.weightsK D BS TT TS hT
  exact present.trans (binary.trans unary)

def typedAppendBinaryRealizationReduction (L : RealLanguage q bt ut)
    (D : Fin dt→Set (Fin q)) (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (newPolicy : Fin dt→Fin dt→Prop)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀i j,IsAlgebraic ℚ (N i j))
    (K : IntermediateField ℚ ℝ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K)
    (NK : Matrix (Fin q) (Fin q) K)
    (hM : ∀l i j,(M l i j:ℝ)=L.matrices l i j)
    (hU : ∀l i,(U l i:ℝ)=L.unaries l i) (hw : ∀i,(w i:ℝ)=L.weights i)
    (hNK : ∀i j,(NK i j:ℝ)=N i j) :
    PromisePolyTimeTuringReduction ((L.appendBinary N hN).typedProblem D (appendOne B newPolicy) T)
      (domainEvaluationProblem basis (appendOne M NK) U w D (appendOne B newPolicy) T) := by
  apply (L.appendBinary N hN).typedPresentationDescentReduction D (appendOne B newPolicy) T
    K basis (appendOne M NK) U w
  · intro l
    refine Fin.addCases (fun k=>?_) (fun k=>?_) l
    · simpa only [appendBinary,appendOne,Fin.addCases_left] using hM k
    · simpa only [appendBinary,appendOne,Fin.addCases_right] using hNK
  · exact hU
  · exact hw

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
