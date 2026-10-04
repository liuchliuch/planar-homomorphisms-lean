import PlanarHom.PositiveClassMomentAvailability
import PlanarHom.WeightedRationalClosure
import PlanarHom.Normalization

/-! The missing joint entrance to the class-moment argument. First append the
original positive background as a literal unary, with background unchanged;
then remove background weights in that enlarged language. Consequently the
unary and every original companion remain available with unit backgrounds. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveClassMomentRigidity
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases PositiveWeightRemoval
open SpectralFieldPresentation
variable {q bt ut : ℕ}

def unitWithWeightUnary (L : RealLanguage q bt ut) : RealLanguage q bt (ut+1) where
  matrices := L.matrices
  unaries := appendOne L.unaries L.weights
  weights := fun _=>1
  matrices_algebraic := L.matrices_algebraic
  unaries_algebraic l := by
    refine Fin.addCases (fun k=>?_) (fun k=>?_) l
    · simpa only [appendOne,Fin.addCases_left] using L.unaries_algebraic k
    · simpa only [appendOne,Fin.addCases_right] using L.weights_algebraic
  weights_algebraic := fun _=>isAlgebraic_one

/-- Actual original weighted-source reduction. The only structural hypotheses
are a positive symmetric unit-diagonal selected matrix with distinct rows.
No invertibility or classification has been assumed at the source entrance. -/
def unitWithWeightUnaryReduction (L : RealLanguage q bt ut) (old : Fin bt)
    (hs : ∀ i j,L.matrices old i j=L.matrices old j i)
    (hpos : ∀ i j,0<L.matrices old i j) (hdiag : ∀ i,L.matrices old i i=1)
    (hinj : Function.Injective (L.matrices old)) (hw : ∀ i,0<L.weights i) :
    PromisePolyTimeTuringReduction (unitWithWeightUnary L).problem L.problem := by
  have hnz : ∀ i,L.matrices old i≠0 := by
    intro i hi
    exact (ne_of_gt (hpos i i)) (congrFun hi i)
  have hproj : ∀ i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j :=
    positive_unitDiagonal_rows_nonproportional _ hpos hs hdiag hinj
  let KP := extensionField L.field (powerAlphabet L.weightsK (1:ℚ))
  let bP := powerBasis L.weightsK hw (1:ℚ)
  letI : FiniteDimensional ℚ KP := FiniteDimensional.of_fintype_basis bP
  let MP := powerMatrices L.matricesK L.weightsK (1:ℚ)
  let UP := powerUnaries L.unariesK L.weightsK (1:ℚ)
  let wP := fun i=>sourceInclusion L.field (powerAlphabet L.weightsK (1:ℚ)) (L.weightsK i)
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
    hs hw hnz hproj (1:ℚ)
  have present := (unitWithWeightUnary L).presentationDescentReduction KP bP
    (MP ∘ Fin.castAdd 1) UP (fun _=>1) hM (by
      intro l
      refine Fin.addCases (fun k=>?_) (fun k=>?_) l
      · intro i
        simp only [UP,powerUnaries,appendOne_old,unitWithWeightUnary]
        rfl
      · intro i
        have hk : k=(0:Fin 1) := Subsingleton.elim _ _
        subst k
        rw [show Fin.natAdd ut (0:Fin 1)=Fin.last ut from Fin.ext rfl]
        simp only [unitWithWeightUnary,appendOne_aux]
        change (powerUnaries L.unariesK L.weightsK 1 (Fin.last ut) i:ℝ)=L.weights i
        rw [powerUnary_real]
        simp) (fun _=>rfl)
  exact present.trans ((binaryRelabelReduction bP (Fin.castAdd 1) MP UP (fun _=>1)).trans
    (remove.trans power))

end PlanarHom.PositiveClassMomentRigidity
