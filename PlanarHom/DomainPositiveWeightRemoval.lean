import PlanarHom.DomainInverseDiagonalAvailability
import PlanarHom.DomainWeightedGramAvailability
import PlanarHom.DomainLoopCancellation
import PlanarHom.PositiveWeightRemovalReduction
import PlanarHom.GlobalDomainSpectralAvailability

/-! Positive background removal on exact prescribed-domain inputs. Original
narrow domains and companion policies are retained. The selected ambient
matrix already admits every domain pair in the source language. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveWeightRemoval
open Complexity Complexity.MixedCode FiniteLanguageAliases SpectralFieldPresentation PrescribedDomains
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q bt ut dt dimension : ℕ}

def skipMiddleAlias (bt : ℕ) : Fin (bt+1)→Fin (bt+1+1) :=
  Fin.lastCases (Fin.last (bt+1)) (fun i=>Fin.castAdd 1 (Fin.castAdd 1 i))

theorem append_skipMiddle {α : Type} (M : Fin bt→α) (N P : α) :
    (appendOne (appendOne M N) P) ∘ skipMiddleAlias bt=appendOne M P := by
  funext l
  refine Fin.lastCases ?_ (fun i=>?_) l
  · simp only [Function.comp_apply,skipMiddleAlias,Fin.lastCases_last,appendOne_aux]
  · simp only [Function.comp_apply,skipMiddleAlias,Fin.lastCases_castSucc]
    change appendOne (appendOne M N) P (Fin.castAdd 1 (Fin.castAdd 1 i))=appendOne M P (Fin.castAdd 1 i)
    simp only [appendOne_old]

def domainSkipMiddleReduction (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt→Matrix (Fin q) (Fin q) K₀) (N P : Matrix (Fin q) (Fin q) K₀)
    (U : Fin ut→Fin q→K₀) (w : Fin q→K₀) (D : Fin dt→Set (Fin q))
    (B : Fin bt→Fin dt→Fin dt→Prop) (BN BP : Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis (appendOne M P) U w D (appendOne B BP) T)
      (domainEvaluationProblem basis (appendOne (appendOne M N) P) U w D (appendOne (appendOne B BN) BP) T) := by
  have htype : ∀i x y,appendOne B BP i x y→appendOne (appendOne B BN) BP (skipMiddleAlias bt i) x y := by
    intro i x y hi
    have he := congrFun (congrFun (congrFun (append_skipMiddle B BN BP) i) x) y
    exact he.mpr hi
  simpa only [append_skipMiddle] using domainBinaryRelabelReduction basis (skipMiddleAlias bt)
    (appendOne (appendOne M N) P) U w D (appendOne B BP) (appendOne (appendOne B BN) BP) T htype

def domainInverseDiagonalFromRows (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt→Matrix (Fin q) (Fin q) K₀) (U : Fin ut→Fin q→K₀) (w : Fin q→K₀)
    (D : Fin dt→Set (Fin q)) (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : D full=Set.univ)
    (hglobal : ∀x y,B old x y)
    (hs : ∀i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw : ∀i,0<(w i : ℝ)) (hnonzero : ∀i,realMatrix (M old) i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹))) U w D (appendOne B (B old)) T)
      (domainEvaluationProblem basis M U w D B T) := by
  let G := gramCoreField (M old) w (max 1 (q-1))
  have hG : (realMatrix G).PosDef := by
    rw [show realMatrix G=gramCore (realMatrix (M old)) (realWeights w) from gramCoreField_real _ _]
    exact gramCore_posDef _ hs _ hw hnonzero hproj
  have hpath : ∀x y,B old x y→PathDomainTyping B old full x y :=
    fun x y _=>⟨hglobal x y,hglobal x full,hglobal full full,hglobal full y⟩
  let hgram := domainGramAppendReduction basis M U w D B T old full hfull hpath (max 1 (q-1))
  have haux : (realMatrix (appendOne M G (Fin.last bt))).PosDef := by simpa only [appendOne_aux] using hG
  have hauxpath : ∀x y,appendOne B (B old) (Fin.last bt) x y→
      PathDomainTyping (appendOne B (B old)) (Fin.last bt) full x y := by
    simpa only [PathDomainTyping,appendOne_aux] using hpath
  have hinv := domainInverseDiagonalAppendReduction basis (appendOne M G) U w D (appendOne B (B old)) T
    (Fin.last bt) full hfull hauxpath haux hw
  simp only [appendOne_aux] at hinv
  exact (domainSkipMiddleReduction basis M G (Matrix.diagonal (fun i=>(w i)⁻¹)) U w D B (B old) (B old) T).trans
    (hinv.trans hgram)

def domainRemovePositiveWeights (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt→Matrix (Fin q) (Fin q) K₀) (U : Fin ut→Fin q→K₀) (w : Fin q→K₀)
    (D : Fin dt→Set (Fin q)) (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : D full=Set.univ) (hglobal : ∀x y,B old x y)
    (hs : ∀i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw : ∀i,0<(w i : ℝ)) (hnonzero : ∀i,realMatrix (M old) i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U (fun _=>1) D B T)
      (domainEvaluationProblem basis M U w D B T) := by
  let A := Matrix.diagonal (fun i=>(w i)⁻¹)
  have he : (appendOne M A) ∘ Fin.castAdd 1=M := by funext l; exact appendOne_old M A l
  have first : PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U (fun _=>1) D B T)
      (domainEvaluationProblem basis (appendOne M A) U (fun _=>1) D (appendOne B (B old)) T) := by
    simpa only [he] using domainBinaryRelabelReduction basis (Fin.castAdd 1) (appendOne M A) U (fun _=>1)
      D B (appendOne B (B old)) T (by intro l x y h; simpa only [appendOne_old] using h)
  have hc : ∀i,w i*appendOne M A (Fin.last bt) i i=1 := by
    intro i
    simp only [appendOne_aux,A,Matrix.diagonal_apply_eq]
    apply mul_inv_cancel₀
    intro h
    exact (ne_of_gt (hw i)) (congrArg (fun x : K₀=>(x:ℝ)) h)
  have second := domainLoopCancellationReduction basis (appendOne M A) U w D (appendOne B (B old)) T
    (Fin.last bt) (by intro x; simpa only [appendOne_aux] using hglobal x x) hc
  exact first.trans (second.trans (domainInverseDiagonalFromRows basis M U w D B T old full hfull hglobal
    hs hw hnonzero hproj))

end PlanarHom.PositiveWeightRemoval
