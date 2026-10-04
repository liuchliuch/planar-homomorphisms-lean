import PlanarHom.FixedRealInterpolationPipeline
import PlanarHom.ComputedMixedInterpolation
import PlanarHom.MixedTotalEvaluation
import PlanarHom.PlanarRibbonExistence
import PlanarHom.GraphCodeNormalization

/-! Literal ordinary-planar binary and unary signature replacement in the
represented fixed-real model. Source zeros and signed product collisions are
handled by the proved semantic identities, with all companion labels retained. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealMixedInterpolation
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension ProductCompatibility
open RepresentedBit
variable {n e q b u:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def problem (M:Fin b→Matrix (Fin q) (Fin q) K) (U:Fin u→Fin q→K) (w:Fin q→K) : Problem :=
  (presentation basis).problem MixedCode.encoding (PlanarValid b u) (totalEvaluation M U w)

def binaryReduction (selected:Fin b) (M M':Fin b→Matrix (Fin q) (Fin q) K)
    (U:Fin u→Fin q→K) (w:Fin q→K)
    (hunchanged:∀l,l.val≠selected.val→M' l=M l)
    (hzero:∀i j,M selected i j=0→M' selected i j=0)
    (hcompat:Compatible (fun p:Fin q×Fin q=>M selected p.1 p.2)
      (fun p:Fin q×Fin q=>M' selected p.1 p.2)) :
    Reduction (problem basis M' U w) (problem basis M U w) := by
  apply FixedRealInterpolationPipeline.reduction basis (binaryAlphabet (M selected)) (binaryAlphabet (M' selected))
    MixedCode.encoding MixedCode.encoding MixedCode.normalizer (PlanarValid b u) (PlanarValid b u)
    (totalEvaluation M' U w) (totalEvaluation M U w) (markedCount selected.val) (parallelLabel selected.val)
    (fp_unaryMarkedCount selected.val) (MixedParallelMachines.fp_parallelLabel selected.val)
  · intro g hg s hs
    exact hg.parallelLabel selected.val s
  · intro g hg
    rw [totalEvaluation_valid M' U w g hg.1]
    have hv: (fun h:Fin (ExponentProductTables.representatives (binaryAlphabet (M selected))
        (binaryAlphabet (M' selected)) (markedCount selected.val g)).length=>
          totalEvaluation M U w (parallelLabel selected.val (h.val+1) g))=
        (fun h=>(g.parallelLabel selected.val (h.val+1)).evaluate
          (parallelLabel_valid selected.val (h.val+1) b u g hg.1) M U w) := by
      funext h
      exact totalEvaluation_valid M U w _ _
    rw [hv]
    exact binary_replacement_from_computed_table g hg.1 selected M M' U w hunchanged
      (fun l i j hl=>by have he:l=selected:=Fin.ext hl; subst l; exact hzero i j) hcompat

def unaryReduction (selected:Fin u) (M:Fin b→Matrix (Fin q) (Fin q) K)
    (U U':Fin u→Fin q→K) (w:Fin q→K)
    (hunchanged:∀l,l.val≠selected.val→U' l=U l)
    (hzero:∀i,U selected i=0→U' selected i=0)
    (hcompat:Compatible (U selected) (U' selected)) :
    Reduction (problem basis M U' w) (problem basis M U w) := by
  apply FixedRealInterpolationPipeline.reduction basis (U selected) (U' selected)
    MixedCode.encoding MixedCode.encoding MixedCode.normalizer (PlanarValid b u) (PlanarValid b u)
    (totalEvaluation M U' w) (totalEvaluation M U w) (unaryMarkedCount selected.val) (parallelUnaryLabel selected.val)
    (fp_unaryMarkedCount_unary selected.val) (fp_parallelUnaryLabel selected.val)
  · intro g hg s hs
    exact hg.parallelUnaryLabel selected.val s
  · intro g hg
    rw [totalEvaluation_valid M U' w g hg.1]
    have hv: (fun h:Fin (ExponentProductTables.representatives (U selected) (U' selected)
        (unaryMarkedCount selected.val g)).length=>
          totalEvaluation M U w (parallelUnaryLabel selected.val (h.val+1) g))=
        (fun h=>(g.parallelUnaryLabel selected.val (h.val+1)).evaluate
          (parallelUnaryLabel_valid selected.val (h.val+1) g hg.1) M U w) := by
      funext h
      exact totalEvaluation_valid M U w _ _
    rw [hv]
    exact unary_replacement_from_computed_table g hg.1 selected M U U' w hunchanged
      (fun l i hl=>by have he:l=selected:=Fin.ext hl; subst l; exact hzero i) hcompat

end PlanarHom.FixedRealMixedInterpolation
