import PlanarHom.DomainPositiveWeightRemoval
import PlanarHom.DiagonalRationalPowerCompatibility

/-! Every fixed rational diagonal is jointly available from the original
weighted source, including negative and zero exponents with off-diagonal zeros. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveWeightRemoval
open Complexity Complexity.MixedCode FiniteLanguageAliases SpectralFieldPresentation
open AlgebraicProductInterpolation ProductCompatibility
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q bt ut dt dimension : ℕ}

def domainRationalDiagonalAppendReduction (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (Domains : Fin dt→Set (Fin q)) (policy : Fin bt→Fin dt→Fin dt→Prop) (typing : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : Domains full=Set.univ) (hglobal : ∀x y,policy old x y) (hs : ∀ i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw : ∀ i,0<(w i : ℝ)) (hnonzero : ∀ i,realMatrix (M old) i≠0)
    (hproj : ∀ i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j) (r : ℚ) :
    let N := diagonalPower (realWeights w) r
    let A := fun p : Fin q × Fin q=>N p.1 p.2
    let φ := sourceInclusion K₀ A
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem (extensionBasis K₀ A (fun p=>diagonalPower_algebraic _ hw
        (fun i=>(Algebra.IsAlgebraic.isAlgebraic (w i)).algHom K₀.val) r p.1 p.2))
        (appendOne (fun l i j=>φ (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹)) l i j))
          (fun i j=>targetValue K₀ A (i,j)))
        (fun l i=>φ (U l i)) (fun i=>φ (w i)) Domains
        (appendOne (appendOne policy (policy old)) (policy old)) typing)
      (domainEvaluationProblem basis M U w Domains policy typing) := by
  dsimp only
  let D := Matrix.diagonal (fun i=>(w i)⁻¹)
  let N := diagonalPower (realWeights w) r
  have hN : ∀ i j,IsAlgebraic ℚ (N i j) := diagonalPower_algebraic _ hw
    (fun i=>(Algebra.IsAlgebraic.isAlgebraic (w i)).algHom K₀.val) r
  have hreal : (fun i j=>(appendOne M D (Fin.last bt) i j : ℝ)) =
      Matrix.diagonal (fun i=>(realWeights w i)⁻¹) := by
    funext i j
    simp only [appendOne_aux]
    by_cases h : i=j
    · subst j
      simp only [D,Matrix.diagonal_apply_eq]
      rfl
    · simp [D,Matrix.diagonal_apply,h]
  have hz : ∀ i j,(appendOne M D (Fin.last bt) i j : ℝ)=0→N i j=0 := by
    intro i j hij
    have he := congrFun (congrFun hreal i) j
    rw [he] at hij
    exact diagonalPower_zero _ hw r i j hij
  have hp : HasProductMaps (fun p : Fin q × Fin q=>(appendOne M D (Fin.last bt) p.1 p.2 : ℝ))
      (fun p=>N p.1 p.2) := by
    have he : (fun p : Fin q × Fin q=>(appendOne M D (Fin.last bt) p.1 p.2 : ℝ)) =
        (fun p=>Matrix.diagonal (fun i=>(realWeights w i)⁻¹) p.1 p.2) := by
      funext p
      exact congrFun (congrFun hreal p.1) p.2
    rw [he]
    exact hasProductMaps_of_compatible _ _ (diagonalPower_compatible _ hw r)
  have result := (domainBinaryOverfieldReduction basis (appendOne M D) U w Domains (appendOne policy (policy old)) typing N hN (Fin.last bt) hz hp).trans
    (domainInverseDiagonalFromRows basis M U w Domains policy typing old full hfull hglobal hs hw hnonzero hproj)
  simpa only [appendOne_aux] using result

end PlanarHom.PositiveWeightRemoval
