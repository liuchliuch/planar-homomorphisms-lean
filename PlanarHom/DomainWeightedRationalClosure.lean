import PlanarHom.WeightedRationalClosure
import PlanarHom.DomainWeightedRationalDiagonal
import PlanarHom.DomainUnaryLoopReduction

/-! All rational diagonal/unary closures with original prescribed domains,
including their actual reserved-label offsets and retained source availability. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveWeightRemoval
open Complexity Complexity.MixedCode FiniteLanguageAliases SpectralFieldPresentation
open AlgebraicProductInterpolation PrescribedDomains
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q bt ut dt dimension : ℕ}

def domainRationalDiagonalUnaryReduction (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt→Matrix (Fin q) (Fin q) K₀) (U : Fin ut→Fin q→K₀) (w : Fin q→K₀)
    (Domains : Fin dt→Set (Fin q)) (policy : Fin bt→Fin dt→Fin dt→Prop) (typing : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : Domains full=Set.univ) (hglobal : ∀x y,policy old x y) (hs : ∀ i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw : ∀ i,0<(w i : ℝ)) (hnonzero : ∀ i,realMatrix (M old) i≠0)
    (hproj : ∀ i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j) (r : ℚ) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem (powerBasis w hw r) (powerMatrices M w r) (powerUnaries U w r)
        (fun i=>sourceInclusion K₀ (powerAlphabet w r) (w i)) Domains (appendOne policy (policy old)) (appendOne typing (fun _=>True)))
      (domainEvaluationProblem basis M U w Domains policy typing) := by
  let A := powerAlphabet w r
  let φ := sourceInclusion K₀ A
  let N : Matrix (Fin q) (Fin q) (extensionField K₀ A) := fun i j=>targetValue K₀ A (i,j)
  let MF : Fin (bt+1)→Matrix (Fin q) (Fin q) (extensionField K₀ A) :=
    fun l i j=>φ (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹)) l i j)
  let UF : Fin ut→Fin q→extensionField K₀ A := fun l i=>φ (U l i)
  let wF : Fin q→extensionField K₀ A := fun i=>φ (w i)
  let big := appendOne MF N
  let UP := appendOne UF (fun i=>N i i)
  let bigPolicy := appendOne (appendOne policy (policy old)) (policy old)
  let UPtyping := appendOne typing (fun _=>True)
  have base : PromisePolyTimeTuringReduction (domainEvaluationProblem (powerBasis w hw r) big UF wF Domains bigPolicy typing)
      (domainEvaluationProblem basis M U w Domains policy typing) :=
    domainRationalDiagonalAppendReduction basis M U w Domains policy typing old full hfull hglobal hs hw hnonzero hproj r
  have last : (fun i=>big (Fin.last (bt+1)) i i)=(fun i=>N i i) := by
    simp only [big,appendOne_aux]
  have unary : PromisePolyTimeTuringReduction (domainEvaluationProblem (powerBasis w hw r) big UP wF Domains bigPolicy UPtyping)
      (domainEvaluationProblem (powerBasis w hw r) big UF wF Domains bigPolicy typing) := by
    simpa only [last] using domainDiagonalUnaryAppendReduction (powerBasis w hw r) big UF wF Domains bigPolicy typing (Fin.last (bt+1)) (fun _=>True)
      (by intro x _; simpa only [bigPolicy,appendOne_aux] using hglobal x x)
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
  have ht : ∀i x y,appendOne policy (policy old) i x y→bigPolicy (ρ i) x y := by
    intro i x y hi
    have hh := congrFun (congrFun (congrFun (append_skipMiddle policy (policy old) (policy old)) i) x) y
    exact hh.mpr hi
  have first : PromisePolyTimeTuringReduction
      (domainEvaluationProblem (powerBasis w hw r) (powerMatrices M w r) UP wF Domains (appendOne policy (policy old)) UPtyping)
      (domainEvaluationProblem (powerBasis w hw r) big UP wF Domains bigPolicy UPtyping) := by
    simpa only [he] using domainBinaryRelabelReduction (powerBasis w hw r) ρ big UP wF Domains
      (appendOne policy (policy old)) bigPolicy UPtyping ht
  exact first.trans (unary.trans base)

end PlanarHom.PositiveWeightRemoval
