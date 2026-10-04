import PlanarHom.WeightedRationalDiagonalAvailability
import PlanarHom.UnaryLoopRealization

/-! The source3.7 rational diagonal and its unary are jointly available with
all original constraints, using the original source field and oracle. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveWeightRemoval
open Complexity Complexity.MixedCode FiniteLanguageAliases SpectralFieldPresentation
open AlgebraicProductInterpolation
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q bt ut dimension : ℕ}

def powerAlphabet (w : Fin q→K₀) (r : ℚ) : Fin q×Fin q→ℝ :=
  fun p=>diagonalPower (realWeights w) r p.1 p.2

def powerBasis (w : Fin q→K₀) (hw : ∀ i,0<(w i : ℝ)) (r : ℚ) :=
  extensionBasis K₀ (powerAlphabet w r) (fun p=>diagonalPower_algebraic _ hw
    (fun i=>(Algebra.IsAlgebraic.isAlgebraic (w i)).algHom K₀.val) r p.1 p.2)

def powerMatrices (M : Fin bt→Matrix (Fin q) (Fin q) K₀) (w : Fin q→K₀) (r : ℚ) :
    Fin (bt+1)→Matrix (Fin q) (Fin q) (extensionField K₀ (powerAlphabet w r)) :=
  appendOne (fun l i j=>sourceInclusion K₀ (powerAlphabet w r) (M l i j))
    (fun i j=>targetValue K₀ (powerAlphabet w r) (i,j))

def powerUnaries (U : Fin ut→Fin q→K₀) (w : Fin q→K₀) (r : ℚ) :
    Fin (ut+1)→Fin q→extensionField K₀ (powerAlphabet w r) :=
  appendOne (fun l i=>sourceInclusion K₀ (powerAlphabet w r) (U l i))
    (fun i=>targetValue K₀ (powerAlphabet w r) (i,i))

def rationalDiagonalUnaryReduction (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt→Matrix (Fin q) (Fin q) K₀) (U : Fin ut→Fin q→K₀) (w : Fin q→K₀)
    (old : Fin bt) (hs : ∀ i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw : ∀ i,0<(w i : ℝ)) (hnonzero : ∀ i,realMatrix (M old) i≠0)
    (hproj : ∀ i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j) (r : ℚ) :
    PromisePolyTimeTuringReduction
      (evaluationProblem (powerBasis w hw r) (powerMatrices M w r) (powerUnaries U w r)
        (fun i=>sourceInclusion K₀ (powerAlphabet w r) (w i)))
      (evaluationProblem basis M U w) := by
  let A := powerAlphabet w r
  let φ := sourceInclusion K₀ A
  let N : Matrix (Fin q) (Fin q) (extensionField K₀ A) := fun i j=>targetValue K₀ A (i,j)
  let MF : Fin (bt+1)→Matrix (Fin q) (Fin q) (extensionField K₀ A) :=
    fun l i j=>φ (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹)) l i j)
  let UF : Fin ut→Fin q→extensionField K₀ A := fun l i=>φ (U l i)
  let wF : Fin q→extensionField K₀ A := fun i=>φ (w i)
  let big := appendOne MF N
  let UP := appendOne UF (fun i=>N i i)
  have base : PromisePolyTimeTuringReduction (evaluationProblem (powerBasis w hw r) big UF wF)
      (evaluationProblem basis M U w) :=
    rationalDiagonalAppendReduction basis M U w old hs hw hnonzero hproj r
  have last : (fun i=>big (Fin.last (bt+1)) i i)=(fun i=>N i i) := by
    simp only [big,appendOne_aux]
  have unary : PromisePolyTimeTuringReduction (evaluationProblem (powerBasis w hw r) big UP wF)
      (evaluationProblem (powerBasis w hw r) big UF wF) := by
    simpa only [last] using diagonalUnaryAppendReduction (powerBasis w hw r) big UF wF (Fin.last (bt+1))
  let ρ : Fin (bt+1)→Fin (bt+1+1) := Fin.lastCases (Fin.last (bt+1))
    (fun i=>Fin.castAdd 1 (Fin.castAdd 1 i))
  have he : big ∘ ρ=powerMatrices M w r := by
    funext l
    refine Fin.lastCases ?_ (fun i=>?_) l
    · simp only [Function.comp_apply,ρ,Fin.lastCases_last,big,powerMatrices,appendOne_aux]
      rfl
    · simp only [Function.comp_apply,ρ,Fin.lastCases_castSucc]
      change appendOne MF N (Fin.castAdd 1 (Fin.castAdd 1 i)) =
        appendOne (fun l j k=>φ (M l j k)) N (Fin.castAdd 1 i)
      simp only [appendOne_old]
      change (fun j k=>φ (appendOne M _ (Fin.castAdd 1 i) j k)) = _
      rw [appendOne_old]
  have first : PromisePolyTimeTuringReduction
      (evaluationProblem (powerBasis w hw r) (powerMatrices M w r) UP wF)
      (evaluationProblem (powerBasis w hw r) big UP wF) := by
    simpa only [he] using binaryRelabelReduction (powerBasis w hw r) ρ big UP wF
  exact first.trans (unary.trans base)

@[simp] theorem powerMatrix_real (M : Fin bt→Matrix (Fin q) (Fin q) K₀)
    (w : Fin q→K₀) (r : ℚ) (i j : Fin q) :
    (powerMatrices M w r (Fin.last bt) i j : ℝ)=diagonalPower (realWeights w) r i j := by
  simp only [powerMatrices,appendOne_aux]
  rfl

@[simp] theorem powerUnary_real (U : Fin ut→Fin q→K₀) (w : Fin q→K₀) (r : ℚ) (i : Fin q) :
    (powerUnaries U w r (Fin.last ut) i : ℝ)=(w i : ℝ)^(r:ℝ) := by
  simp only [powerUnaries,appendOne_aux]
  change diagonalPower (realWeights w) r i i=_
  simp only [diagonalPower,Matrix.diagonal_apply_eq,realWeights]

end PlanarHom.PositiveWeightRemoval
