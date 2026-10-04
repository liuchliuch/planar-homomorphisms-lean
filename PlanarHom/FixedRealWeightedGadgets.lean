import PlanarHom.FixedRealMixedAliases
import PlanarHom.WeightedGramAvailability
import PlanarHom.LoopCancellationReduction
import PlanarHom.DenseRationalConstantExtraction

/-! NEW represented-field versions of the literal Gram gadget and inverse-loop
cancellation. The field is finite over a rational-function field, with arbitrary
valid answer representatives and all mixed labels retained. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealWeightedGadgets
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open FixedRealMixedInterpolation PositiveWeightRemoval FiniteLanguageAliases
variable {n e q bt ut:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def gramAppendReduction (M:Fin bt→Matrix (Fin q) (Fin q) K) (U:Fin ut→Fin q→K)
    (w:Fin q→K) (old:Fin bt) (p:ℕ) :
    Reduction (problem basis (appendOne M (gramCoreField (M old) w p)) U w)
      (problem basis M U w) := by
  letI : Algebra ℚ K := ((algebraMap (RationalFunction n) K).comp
    (DenseRationalConstantExtraction.constantMap n)).toAlgebra
  apply queryReduction (presentation basis) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
    (PlanarValid (bt+1) ut) (PlanarValid bt ut)
    (totalEvaluation (appendOne M (gramCoreField (M old) w p)) U w) (totalEvaluation M U w)
    (gramTransform bt old.val p) (fp_gramTransform old.val p)
  · intro g hg
    exact gramTransform_planar g hg old p
  · intro g hg
    rw [totalEvaluation_valid _ _ _ g hg.1]
    exact gramTransform_evaluate g hg.1 M U w old p

def loopCancellationReduction (M:Fin bt→Matrix (Fin q) (Fin q) K) (U:Fin ut→Fin q→K)
    (w:Fin q→K) (selected:Fin bt) (hcancel:∀i,w i*M selected i i=1) :
    Reduction (problem basis M U (fun _=>1)) (problem basis M U w) := by
  apply queryReduction (presentation basis) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
    (PlanarValid bt ut) (PlanarValid bt ut) (totalEvaluation M U (fun _=>1)) (totalEvaluation M U w)
    (MixedCode.addLoops selected.val) (fp_addLoops selected.val)
  · intro g hg
    exact addLoops_planar selected.val selected.isLt g hg
  · intro g hg
    rw [totalEvaluation_valid _ _ _ _ (addLoops_valid selected g hg.1),
      evaluate_addLoops selected g hg.1,totalEvaluation_valid _ _ _ g hg.1]
    simp only [hcancel]

def skipMiddleReduction (M:Fin bt→Matrix (Fin q) (Fin q) K) (N P:Matrix (Fin q) (Fin q) K)
    (U:Fin ut→Fin q→K) (w:Fin q→K) :
    Reduction (problem basis (appendOne M P) U w) (problem basis (appendOne (appendOne M N) P) U w) := by
  let ρ:Fin (bt+1)→Fin (bt+1+1):=Fin.lastCases (Fin.last (bt+1))
    (fun i=>Fin.castAdd 1 (Fin.castAdd 1 i))
  have he:(appendOne (appendOne M N) P)∘ρ=appendOne M P := by
    funext l
    refine Fin.lastCases ?_ (fun i=>?_) l
    · simp [ρ,Function.comp_def,appendOne_aux]
    · simp only [Function.comp_apply,ρ,Fin.lastCases_castSucc]
      change appendOne (appendOne M N) P (Fin.castAdd 1 (Fin.castAdd 1 i))=appendOne M P (Fin.castAdd 1 i)
      simp only [appendOne_old]
  simpa only [he] using FixedRealMixedInterpolation.binaryRelabelReduction basis ρ (appendOne (appendOne M N) P) U w

end PlanarHom.FixedRealWeightedGadgets
