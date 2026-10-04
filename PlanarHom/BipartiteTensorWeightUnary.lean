-- Recovered proof bodies; identical endpoint-unary use adapted to sameReduction.
import PlanarHom.PositiveClassMomentAvailability
import PlanarHom.WeightedRationalClosure
import PlanarHom.Normalization
import PlanarHom.AlgebraicLanguageExtensions
import PlanarHom.ZeroOneGramSourceAvailability

/-! Actual unit-background square-root-weight unary entrance. First append the
square root of the original positive background as a literal unary, with background unchanged;
then remove background weights in that enlarged language. Consequently the
unary and every original companion remain available with unit backgrounds. -/
noncomputable section
open Classical
namespace PlanarHom.BipartiteTensorWeight
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases PositiveWeightRemoval
open SpectralFieldPresentation
variable {q bt ut : ℕ}

def unitWithSqrtWeightUnary (L : RealLanguage q bt ut) (hw : ∀ i,0<L.weights i) : RealLanguage q bt (ut+1) where
  matrices := L.matrices
  unaries := appendOne L.unaries (fun i=>Real.sqrt (L.weights i))
  weights := fun _=>1
  matrices_algebraic := L.matrices_algebraic
  unaries_algebraic l := by
    refine Fin.addCases (fun k=>?_) (fun k=>?_) l
    · simpa only [appendOne,Fin.addCases_left] using L.unaries_algebraic k
    · simpa only [appendOne,Fin.addCases_right] using (fun i=>BooleanPDNormalization.isAlgebraic_sqrt (hw i).le (L.weights_algebraic i))
  weights_algebraic := fun _=>isAlgebraic_one

/-- Actual original weighted-source reduction. The structural hypotheses are symmetry, nonzero rows, and pairwise nonproportional rows.
No invertibility or classification has been assumed at the source entrance. -/
def unitWithSqrtWeightUnaryReduction (L : RealLanguage q bt ut) (old : Fin bt)
    (hs : ∀ i j,L.matrices old i j=L.matrices old j i)
    (hnz : ∀ i,L.matrices old i≠0)
    (hproj : ∀ i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (hw : ∀ i,0<L.weights i) :
    PromisePolyTimeTuringReduction (unitWithSqrtWeightUnary L hw).problem L.problem := by
  let KP := extensionField L.field (powerAlphabet L.weightsK (1/2:ℚ))
  let bP := powerBasis L.weightsK hw (1/2:ℚ)
  letI : FiniteDimensional ℚ KP := FiniteDimensional.of_fintype_basis bP
  let MP := powerMatrices L.matricesK L.weightsK (1/2:ℚ)
  let UP := powerUnaries L.unariesK L.weightsK (1/2:ℚ)
  let wP := fun i=>sourceInclusion L.field (powerAlphabet L.weightsK (1/2:ℚ)) (L.weightsK i)
  have hM : ∀ l i j,(MP (Fin.castAdd 1 l) i j:ℝ)=L.matrices l i j := by
    intro l i j
    simp only [MP,powerMatrices,appendOne_old]
    rfl
  have hReal : realMatrix (MP (Fin.castAdd 1 old))=L.matrices old := by
    ext i j
    exact hM old i j
  have hsP : ∀ i j,realMatrix (MP (Fin.castAdd 1 old)) i j=
      realMatrix (MP (Fin.castAdd 1 old)) j i := by
    intro i j
    simpa only [hReal] using hs i j
  have hnzP : ∀ i,realMatrix (MP (Fin.castAdd 1 old)) i≠0 := by
    simpa only [hReal] using hnz
  have hprojP : ∀ i j,i≠j→∀t:ℝ,realMatrix (MP (Fin.castAdd 1 old)) i≠
      t • realMatrix (MP (Fin.castAdd 1 old)) j := by
    simpa only [hReal] using hproj
  have remove := removePositiveWeights bP MP UP wP (Fin.castAdd 1 old)
    hsP hw hnzP hprojP
  have power := rationalDiagonalUnaryReduction L.basis L.matricesK L.unariesK L.weightsK old
    hs hw hnz hproj (1/2:ℚ)
  have present := (unitWithSqrtWeightUnary L hw).presentationDescentReduction KP bP
    (MP ∘ Fin.castAdd 1) UP (fun _=>1) hM (by
      intro l
      refine Fin.addCases (fun k=>?_) (fun k=>?_) l
      · intro i
        simp only [UP,powerUnaries,appendOne_old,unitWithSqrtWeightUnary]
        rfl
      · intro i
        have hk : k=(0:Fin 1) := Subsingleton.elim _ _
        subst k
        rw [show Fin.natAdd ut (0:Fin 1)=Fin.last ut from Fin.ext rfl]
        simp only [unitWithSqrtWeightUnary,appendOne_aux]
        change (powerUnaries L.unariesK L.weightsK (1/2) (Fin.last ut) i:ℝ)=Real.sqrt (L.weights i)
        rw [powerUnary_real,Real.sqrt_eq_rpow]
        norm_num) (fun _=>rfl)
  exact present.trans ((binaryRelabelReduction bP (Fin.castAdd 1) MP UP (fun _=>1)).trans
    (remove.trans power))


def decoratedMatrix (L : RealLanguage q bt ut) (old : Fin bt) : Matrix (Fin q) (Fin q) ℝ :=
  EndpointUnaryGauge.decorated (L.matrices old) (fun i=>Real.sqrt (L.weights i))
    (fun i=>Real.sqrt (L.weights i))

theorem decoratedMatrix_algebraic (L : RealLanguage q bt ut) (old : Fin bt)
    (hw : ∀ i,0<L.weights i) : ∀ i j,IsAlgebraic ℚ (decoratedMatrix L old i j) := by
  intro i j
  exact ((BooleanPDNormalization.isAlgebraic_sqrt (hw i).le (L.weights_algebraic i)).mul
    (L.matrices_algebraic old i j)).mul
    (BooleanPDNormalization.isAlgebraic_sqrt (hw j).le (L.weights_algebraic j))

def decoratedLanguage (L : RealLanguage q bt ut) (old : Fin bt) (hw : ∀ i,0<L.weights i) :
    RealLanguage q 1 0 :=
  unitLanguage (fun _=>decoratedMatrix L old) (fun _=>decoratedMatrix_algebraic L old hw)

/-- Both endpoint factors are attached to every edge occurrence, including
loops. The canonical target field is explicitly descended to the unary field. -/
def decoratedSourceReduction (L : RealLanguage q bt ut) (old : Fin bt)
    (hs : ∀ i j,L.matrices old i j=L.matrices old j i)
    (hnz : ∀ i,L.matrices old i≠0)
    (hproj : ∀ i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (hw : ∀ i,0<L.weights i) :
    PromisePolyTimeTuringReduction (decoratedLanguage L old hw).problem L.problem := by
  let S := unitWithSqrtWeightUnary L hw
  let N := decoratedMatrix L old
  let T := S.appendBinary N (decoratedMatrix_algebraic L old hw)
  have r₁ := (decoratedLanguage L old hw).relabelReduction T (fun _=>Fin.last bt)
    (fun u=>u.elim0) (by
      intro l i j
      simp only [decoratedLanguage,unitLanguage,T,appendBinary,appendOne_aux,N])
    (fun u=>u.elim0) (fun _=>rfl)
  let NK := EndpointUnaryGauge.decorated (S.matricesK old)
    (S.unariesK (Fin.last ut)) (S.unariesK (Fin.last ut))
  have hNK : ∀ i j,(NK i j:ℝ)=N i j := by
    intro i j
    simp only [NK,EndpointUnaryGauge.decorated,IntermediateField.coe_mul]
    change S.unaries (Fin.last ut) i*S.matrices old i j*S.unaries (Fin.last ut) j=N i j
    simp only [S,unitWithSqrtWeightUnary,appendOne_aux,N,decoratedMatrix,EndpointUnaryGauge.decorated]
  have r₂ := S.appendBinaryRealizationReduction N (decoratedMatrix_algebraic L old hw)
    S.field S.basis S.matricesK S.unariesK S.weightsK NK
    (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _=>rfl) hNK
  exact r₁.trans (r₂.trans ((EndpointUnaryGauge.sameReduction S.basis S.matricesK S.unariesK
    S.weightsK old (Fin.last ut)).trans
    (unitWithSqrtWeightUnaryReduction L old hs hnz hproj hw)))

def squareLanguage (L : RealLanguage q bt ut) (old : Fin bt) (hw : ∀ i,0<L.weights i) :
    RealLanguage q 1 0 := (decoratedLanguage L old hw).gramLanguage 1

theorem squareLanguage_matrix (L : RealLanguage q bt ut) (old : Fin bt)
    (hw : ∀ i,0<L.weights i) :
    (squareLanguage L old hw).matrices 0=decoratedMatrix L old*decoratedMatrix L old := by
  ext i j
  simp [squareLanguage,gramLanguage,gramMatrix,gramCoreField,decoratedLanguage,unitLanguage,
    Matrix.diagonal_one]

def squareSourceReduction (L : RealLanguage q bt ut) (old : Fin bt)
    (hs : ∀ i j,L.matrices old i j=L.matrices old j i)
    (hnz : ∀ i,L.matrices old i≠0)
    (hproj : ∀ i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (hw : ∀ i,0<L.weights i) :
    PromisePolyTimeTuringReduction (squareLanguage L old hw).problem L.problem :=
  ((decoratedLanguage L old hw).gramSourceReduction (fun _=>rfl) 1).trans
    (decoratedSourceReduction L old hs hnz hproj hw)

end PlanarHom.BipartiteTensorWeight
