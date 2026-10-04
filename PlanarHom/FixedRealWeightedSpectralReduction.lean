import PlanarHom.FixedRealWeightedGadgets
import PlanarHom.WeightedSpectralAppendReduction

/-! NEW actual weighted-chain spectral interpolation in the represented fixed
real model. It uses the certified variable-order extension solver and concrete
positive-length path queries, with unchanged mixed companion constraints. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealWeightedGadgets
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open FixedRealMixedInterpolation ProductCompatibility FiniteLanguageAliases
variable {n e q bt ut t:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def spectralAppendReduction (M:Fin bt→Matrix (Fin q) (Fin q) K) (U:Fin ut→Fin q→K)
    (w:Fin q→K) (old:Fin bt) (P:Fin t→Matrix (Fin q) (Fin q) K) (a b:Fin t→K)
    (hchains:∀s:ℕ,0<s→weightedChain (M old) w s=∑i,a i^s • P i)
    (hzero:∀i,a i=0→b i=0) (hcompat:Compatible a b) :
    Reduction (problem basis (appendOne M (∑i,b i • P i)) U w) (problem basis M U w) := by
  let transform:ℕ→MixedCode→MixedCode:=fun s g=>g.stretchLabelLength bt old.val s
  apply FixedRealInterpolationPipeline.reduction basis a b MixedCode.encoding MixedCode.encoding
    MixedCode.normalizer (PlanarValid (bt+1) ut) (PlanarValid bt ut)
    (totalEvaluation (appendOne M (∑i,b i • P i)) U w) (totalEvaluation M U w)
    (markedCount bt) transform (fp_unaryMarkedCount bt) (fp_stretchLabelLength bt old.val)
  · intro g hg s hs
    exact g.stretchLabelLength_planar hg bt s old (g.appended_companion_bound hg.1)
  · intro g hg
    rw [totalEvaluation_valid _ _ _ g hg.1]
    have hq (s:ℕ) (hs:0<s) : totalEvaluation M U w (transform s g)=
        g.evaluate hg.1 (spectralLabels (appendOne M (M old)) (Fin.last bt) P (fun i=>a i^s)) U w := by
      change totalEvaluation M U w (g.stretchLabelLength bt old.val s)=_
      rw [totalEvaluation_valid _ _ _ _ (g.stretchLabelLength_valid hg.1 bt s old (g.appended_companion_bound hg.1))]
      rw [g.evaluate_stretchLabelLength_weighted hg.1 old s M U w,hchains s hs]
      congr 1
      exact (replace_last_appendOne M (M old) _).symm
    have he:(fun h:Fin (ExponentProductTables.representatives a b (g.markedCount bt)).length=>
        totalEvaluation M U w (transform (h.val+1) g))=
      (fun h=>g.evaluate hg.1 (spectralLabels (appendOne M (M old)) (Fin.last bt) P (fun i=>a i^(h.val+1))) U w) := by
      funext h
      exact hq (h.val+1) (by omega)
    rw [he]
    have hh:=spectral_replacement_from_computed_table g hg.1 (Fin.last bt)
      (appendOne M (M old)) U w P a b hzero hcompat
    have hl : spectralLabels (appendOne M (M old)) (Fin.last bt) P b =
        appendOne M (∑i,b i • P i) := replace_last_appendOne M (M old) _
    rw [hl] at hh
    exact hh

end PlanarHom.FixedRealWeightedGadgets
