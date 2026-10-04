import PlanarHom.BooleanBiasedFactorReduction
import PlanarHom.BooleanParameterClasses
import PlanarHom.AlgebraicProductOverfield
import PlanarHom.BooleanPDNormalization
import PlanarHom.PromisedSharpPHardness

/-! NEW original-source assembly for the unequal-factor branch of Theorem 5.1.
Normalization, the fixed compositum, exact repeated-parameter classes, source
queries and root extraction are concrete. Independent Boolean counting hardness
remains an explicit separate foundation until its planar reduction is supplied. -/
noncomputable section
open Classical
namespace PlanarHom.BooleanTensorSourceAssembly
open Complexity Complexity.MixedCode AlgebraicProductInterpolation FiniteLanguageAliases
open BooleanPDNormalization BooleanParameterClasses

structure BiasedBooleanReduction (base : PromiseProblem) where
  field : IntermediateField ℚ ℝ
  finite : FiniteDimensional ℚ field
  dimension : ℕ
  basis : Module.Basis (Fin dimension) ℚ field
  matrix : Matrix Bool Bool field
  symmetric : ∀i j,matrix i j=matrix j i
  positive : ∀i j,0<(matrix i j:ℝ)
  biased : matrix false false≠matrix true true
  determinant : matrix false false*matrix true true≠matrix false true^2
  reduction : PromisePolyTimeTuringReduction
    (evaluationProblem basis (fun _:Fin 1=>matrix) (fun u:Fin 0=>u.elim0) (fun _=>1)) base

def parameterConstants {d : ℕ} (γ : ℝ) (θ w : Fin d→ℝ) : Unit ⊕ (Fin d×Bool)→ℝ
  | .inl _=>γ
  | .inr (r,false)=>θ r
  | .inr (r,true)=>w r

theorem parameterConstants_algebraic {d : ℕ} (γ : ℝ) (θ w : Fin d→ℝ)
    (hγ:IsAlgebraic ℚ γ) (hθ:∀r,IsAlgebraic ℚ (θ r)) (hw:∀r,IsAlgebraic ℚ (w r)) :
    ∀i,IsAlgebraic ℚ (parameterConstants γ θ w i) := by
  intro i
  rcases i with u | ⟨r,b⟩
  · exact hγ
  · cases b
    · exact hθ r
    · exact hw r

theorem normalized_source {q bt ut d : ℕ} (L : RealLanguage q bt ut)
    (hunit:∀i,L.weights i=1) (old : Fin bt) (e : Fin q≃Boolean.Cube d)
    (γ : ℝ) (hγ:0<γ) (hγalg:IsAlgebraic ℚ γ)
    (θ w : Fin d→ℝ) (hθ:∀r,1≤θ r) (hw:∀r,0<w r) (hw1:∀r,w r<1)
    (hθalg:∀r,IsAlgebraic ℚ (θ r)) (hwalg:∀r,IsAlgebraic ℚ (w r))
    (hsource:Matrix.reindex e e (L.matrices old)=
      γ • CubeTensorExponential.tensor (fun r=>normalForm (θ r) (w r)))
    (hbias:∃r,1<θ r) : Nonempty (BiasedBooleanReduction L.problem) := by
  let constants:=parameterConstants γ θ w
  have halg:=parameterConstants_algebraic γ θ w hγalg hθalg hwalg
  let K:=extensionField L.field constants
  letI:FiniteDimensional ℚ K:=extension_finiteDimensional L.field constants halg
  let basis:=extensionBasis L.field constants halg
  let φ:=sourceInclusion L.field constants
  let M:=fun l i j=>φ (L.matricesK l i j)
  let U:=fun l i=>φ (L.unariesK l i)
  let γK:K:=targetValue L.field constants (.inl ())
  let θK:Fin d→K:=fun r=>targetValue L.field constants (.inr (r,false))
  let wK:Fin d→K:=fun r=>targetValue L.field constants (.inr (r,true))
  let cls:=classOf θK wK
  let th:=fun i=>(representative θK wK i).1
  let ww:=fun i=>(representative θK wK i).2
  have hrepc:∀r,(th (cls r),ww (cls r))=(θK r,wK r):=representative_classOf θK wK
  have hth:∀i,1≤(th i:ℝ):=by
    intro i
    obtain ⟨r,hr⟩:=representative_has_coordinate θK wK i
    change 1≤((representative θK wK i).1:ℝ)
    rw [hr]
    exact hθ r
  have hww:∀i,0<(ww i:ℝ):=by
    intro i
    obtain ⟨r,hr⟩:=representative_has_coordinate θK wK i
    change 0<((representative θK wK i).2:ℝ)
    rw [hr]
    exact hw r
  have hww1:∀i,(ww i:ℝ)<1:=by
    intro i
    obtain ⟨r,hr⟩:=representative_has_coordinate θK wK i
    change ((representative θK wK i).2:ℝ)<1
    rw [hr]
    exact hw1 r
  have hrep:Function.Injective (fun i=>((th i:ℝ),(ww i:ℝ))):=by
    intro i j h
    apply representative_injective θK wK
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact Subtype.ext (congrArg Prod.snd h)
  have hs:Matrix.reindex e e (SpectralFieldPresentation.realMatrix (M old))=
      (γK:ℝ) • CubeTensorExponential.tensor (fun r=>normalForm (th (cls r):ℝ) (ww (cls r):ℝ)):=by
    have ht:∀r,th (cls r)=θK r:=fun r=>congrArg Prod.fst (hrepc r)
    have hw':∀r,ww (cls r)=wK r:=fun r=>congrArg Prod.snd (hrepc r)
    simp_rw [ht,hw']
    exact hsource
  obtain ⟨r0,hr0⟩:=hbias
  have h0:1<(th (cls r0):ℝ):=by
    rw [show th (cls r0)=θK r0 from congrArg Prod.fst (hrepc r0)]
    exact hr0
  obtain ⟨B,hsym,hpos,hneq,hdet,⟨red⟩⟩:=BooleanBiasedFactorReduction.exists_biased_factor
    basis M U old e γK hγ cls th ww hth hww hww1 hrep hs (cls r0) h0 ⟨r0,rfl⟩
  have source:PromisePolyTimeTuringReduction (evaluationProblem basis M U (fun _=>1)) L.problem:=by
    have r:=fieldMapReduction L.basis basis φ L.matricesK L.unariesK (fun _=>1)
    simpa only [RealLanguage.problem,RealLanguage.weightsK_eq_one L hunit,map_one] using r
  exact ⟨⟨K,inferInstance,_,basis,B,hsym,hpos,hneq,hdet,red.trans source⟩⟩

/-- All normalization hypotheses are derived from the actual positive-definite
Boolean factors and their original algebraic entries. -/
theorem scaled_tensor_source {q bt ut d : ℕ} (L : RealLanguage q bt ut)
    (hunit:∀i,L.weights i=1) (old : Fin bt) (e : Fin q≃Boolean.Cube d)
    (F : Fin d→Matrix Bool Bool ℝ) (hF:∀r,(F r).PosDef)
    (hpos:∀r i j,0<F r i j) (halg:∀r i j,IsAlgebraic ℚ (F r i j))
    (γ : ℝ) (hγ:0<γ) (hγalg:IsAlgebraic ℚ γ)
    (hsource:Matrix.reindex e e (L.matrices old)=γ • CubeTensorExponential.tensor F)
    (hbias:∃r,F r false false≠F r true true) : Nonempty (BiasedBooleanReduction L.problem) := by
  let en:=e.trans (tensorColorOrder F)
  let θ:=fun r=>theta (orderedFactor (F r))
  let w:=fun r=>weight (orderedFactor (F r))
  obtain ⟨htensor,hscale,hparams,hfields⟩:=normalized_tensor_spec F hF hpos
  have hnorm:Matrix.reindex en en (L.matrices old)=
      (γ*tensorScale F) • CubeTensorExponential.tensor (fun r=>normalForm (θ r) (w r)):=by
    change Matrix.reindex (tensorColorOrder F) (tensorColorOrder F)
      (Matrix.reindex e e (L.matrices old))=_
    rw [hsource]
    change γ • Matrix.reindex (tensorColorOrder F) (tensorColorOrder F)
      (CubeTensorExponential.tensor F)=_
    rw [htensor,smul_smul]
  apply normalized_source L hunit old en (γ*tensorScale F) (mul_pos hγ hscale)
    (hγalg.mul (hfields halg).1) θ w (fun r=>(hparams r).1)
    (fun r=>(hparams r).2.1) (fun r=>(hparams r).2.2.1)
    (fun r=>((hfields halg).2 r).1) (fun r=>((hfields halg).2 r).2) hnorm
  obtain ⟨r,hr⟩:=hbias
  exact ⟨r,(hparams r).2.2.2.mpr hr⟩

/-- The independently stated positive biased Boolean hardness input. This file
does not construct an inhabitant or declare it as an axiom. -/
def BiasedBooleanFoundation : Prop :=
  ∀ (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K] (dimension : ℕ)
    (basis : Module.Basis (Fin dimension) ℚ K) (B : Matrix Bool Bool K),
    (∀i j,B i j=B j i)→(∀i j,0<(B i j:ℝ))→B false false≠B true true→
    B false false*B true true≠B false true^2→
    PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>B) (fun u:Fin 0=>u.elim0) (fun _=>1))

theorem hardness_of_reduction (hfoundation:BiasedBooleanFoundation) (base : PromiseProblem)
    (h:Nonempty (BiasedBooleanReduction base)) : PromisedSharpPHard base := by
  obtain ⟨r⟩:=h
  letI:=r.finite
  exact (hfoundation r.field r.dimension r.basis r.matrix r.symmetric r.positive r.biased r.determinant).trans r.reduction

theorem scaled_tensor_hard_of_foundation {q bt ut d : ℕ} (hfoundation:BiasedBooleanFoundation)
    (L : RealLanguage q bt ut) (hunit:∀i,L.weights i=1) (old : Fin bt) (e : Fin q≃Boolean.Cube d)
    (F : Fin d→Matrix Bool Bool ℝ) (hF:∀r,(F r).PosDef)
    (hpos:∀r i j,0<F r i j) (halg:∀r i j,IsAlgebraic ℚ (F r i j))
    (γ : ℝ) (hγ:0<γ) (hγalg:IsAlgebraic ℚ γ)
    (hsource:Matrix.reindex e e (L.matrices old)=γ • CubeTensorExponential.tensor F)
    (hbias:∃r,F r false false≠F r true true) : PromisedSharpPHard L.problem :=
  hardness_of_reduction hfoundation L.problem
    (scaled_tensor_source L hunit old e F hF hpos halg γ hγ hγalg hsource hbias)

end PlanarHom.BooleanTensorSourceAssembly
