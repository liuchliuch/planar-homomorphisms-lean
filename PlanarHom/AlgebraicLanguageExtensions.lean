import PlanarHom.AlgebraicLanguagePresentation
import PlanarHom.MixedLabelAliasReductions

/-! Concrete canonical-language extension and contextual label transport.
Changing the finite fixed alphabet never silently identifies its chosen field
codec with an old or larger presentation. Every bridge is an actual machine. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases
variable {q bt ut bs us dimension : ℕ}

def appendBinary (L : RealLanguage q bt ut) (N : Matrix (Fin q) (Fin q) ℝ)
    (hN : ∀ i j,IsAlgebraic ℚ (N i j)) : RealLanguage q (bt+1) ut where
  matrices := appendOne L.matrices N
  unaries := L.unaries
  weights := L.weights
  matrices_algebraic l := by
    refine Fin.addCases (fun k=>?_) (fun k=>?_) l
    · simpa only [appendOne,Fin.addCases_left] using L.matrices_algebraic k
    · simpa only [appendOne,Fin.addCases_right] using hN
  unaries_algebraic := L.unaries_algebraic
  weights_algebraic := L.weights_algebraic

theorem appendBinary_congr (L : RealLanguage q bt ut)
    (N M : Matrix (Fin q) (Fin q) ℝ)
    (hN : ∀ i j,IsAlgebraic ℚ (N i j)) (hM : ∀ i j,IsAlgebraic ℚ (M i j))
    (h : N=M) : L.appendBinary N hN=L.appendBinary M hM := by
  subst M
  rfl

/-- Any literal typed label map yields a canonical-to-canonical reduction,
including real field/basis conversion and arbitrary retained companions. -/
def relabelReduction (T : RealLanguage q bt ut) (S : RealLanguage q bs us)
    (rb : Fin bt → Fin bs) (ru : Fin ut → Fin us)
    (hM : ∀ l i j,T.matrices l i j=S.matrices (rb l) i j)
    (hU : ∀ l i,T.unaries l i=S.unaries (ru l) i)
    (hw : ∀ i,T.weights i=S.weights i) :
    PromisePolyTimeTuringReduction T.problem S.problem := by
  have present := T.presentationDescentReduction S.field S.basis
    (S.matricesK ∘ rb) (S.unariesK ∘ ru) S.weightsK
    (fun l i j=>(hM l i j).symm) (fun l i=>(hU l i).symm) (fun i=>(hw i).symm)
  have rbR := binaryRelabelReduction S.basis rb S.matricesK (S.unariesK ∘ ru) S.weightsK
  have ruR := unaryRelabelReduction S.basis ru S.matricesK S.unariesK S.weightsK
  exact present.trans (rbR.trans ruR)

/-- The natural field of an appended language can be represented in any fixed
field containing both the old language and the new literal matrix. -/
def appendBinaryRealizationReduction (L : RealLanguage q bt ut)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀ i j,IsAlgebraic ℚ (N i j))
    (K : IntermediateField ℚ ℝ) (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (NK : Matrix (Fin q) (Fin q) K)
    (hM : ∀ l i j,(M l i j:ℝ)=L.matrices l i j)
    (hU : ∀ l i,(U l i:ℝ)=L.unaries l i) (hw : ∀ i,(w i:ℝ)=L.weights i)
    (hNK : ∀ i j,(NK i j:ℝ)=N i j) :
    PromisePolyTimeTuringReduction (L.appendBinary N hN).problem
      (evaluationProblem basis (appendOne M NK) U w) := by
  apply (L.appendBinary N hN).presentationDescentReduction K basis (appendOne M NK) U w
  · intro l
    refine Fin.addCases (fun k=>?_) (fun k=>?_) l
    · simpa only [appendBinary,appendOne,Fin.addCases_left] using hM k
    · simpa only [appendBinary,appendOne,Fin.addCases_right] using hNK
  · exact hU
  · exact hw

/-- The old overfield output of Lemma3.1 is converted into the exact natural
field presentation of the literal appended real language. -/
def appendBinaryOverfieldReduction (L : RealLanguage q bt ut)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀ i j,IsAlgebraic ℚ (N i j)) :
    PromisePolyTimeTuringReduction (L.appendBinary N hN).problem (L.binaryTargetProblem N hN) := by
  let A := fun p : Fin q×Fin q=>N p.1 p.2
  let φ := sourceInclusion L.field A
  exact L.appendBinaryRealizationReduction N hN (extensionField L.field A)
    (extensionBasis L.field A (fun p=>hN p.1 p.2))
    (fun l i j=>φ (L.matricesK l i j)) (fun l i=>φ (L.unariesK l i)) (fun i=>φ (L.weightsK i))
    (fun i j=>targetValue L.field A (i,j))
    (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _=>rfl) (fun _ _=>rfl)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
