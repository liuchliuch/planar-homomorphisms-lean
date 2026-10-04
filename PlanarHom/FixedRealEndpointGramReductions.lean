import PlanarHom.RepresentedReductionComposition
import PlanarHom.FixedRealMixedAliases
import PlanarHom.EndpointUnarySource
import PlanarHom.FixedRealWeightedGadgets

/-! Actual endpoint-unary and two-edge square programs for A.10/A.11. Every
old label is retained, and each loop receives both endpoint unary occurrences.
These are proved graph transformations, not supplied gadget capabilities. -/
noncomputable section
namespace PlanarHom.FixedRealEndpointGrams
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open FixedRealMixedInterpolation FiniteLanguageAliases EndpointUnarySource
variable {n e q bt ut:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def endpointAppendReduction (M:Fin bt→Matrix (Fin q) (Fin q) K) (U:Fin ut→Fin q→K) (w:Fin q→K)
    (old:Fin bt) (unary:Fin ut) :
    Reduction (problem basis (appendOne M (unaryGauge (M old) (U unary))) U w) (problem basis M U w) := by
  apply queryReduction (presentation basis) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
    (PlanarValid (bt+1) ut) (PlanarValid bt ut)
    (totalEvaluation (appendOne M (unaryGauge (M old) (U unary))) U w) (totalEvaluation M U w)
    (endpointTransform old unary) (fp_endpointTransform old unary)
  · exact endpointTransform_planar old unary
  · intro g hg
    rw [totalEvaluation_valid _ _ _ _ (endpointTransform_planar old unary g hg).1,
      totalEvaluation_valid _ _ _ g hg.1]
    exact evaluate_endpointTransform old unary g hg.1 M U w _

def selectReduction (M:Fin bt→Matrix (Fin q) (Fin q) K) (U:Fin ut→Fin q→K) (w:Fin q→K) (old:Fin bt) :
    Reduction (problem basis (fun _:Fin 1=>M old) (fun i:Fin 0=>i.elim0) w) (problem basis M U w) := by
  have hu:=unaryRelabelReduction basis (fun i:Fin 0=>i.elim0) (fun _:Fin 1=>M old) U w
  have he:U∘(fun i:Fin 0=>i.elim0)=(fun i:Fin 0=>(i.elim0:Fin q→K)) := by
    funext i; exact i.elim0
  rw [he] at hu
  exact hu.trans (binaryRelabelReduction basis (fun _:Fin 1=>old) M U w)

def squareDecorationReduction (M:Fin bt→Matrix (Fin q) (Fin q) K)
    (U:Fin ut→Fin q→K) (old:Fin bt) (unary:Fin ut) :
    Reduction (problem basis (fun _:Fin 1=>(unaryGauge (M old) (U unary))^2)
      (fun i:Fin 0=>i.elim0) (fun _=>1)) (problem basis M U (fun _=>1)) := by
  let D:=unaryGauge (M old) (U unary)
  let MD:=appendOne M D
  have hg:=FixedRealWeightedGadgets.gramAppendReduction basis MD U (fun _=>1) (Fin.last bt) 1
  have he:PositiveWeightRemoval.gramCoreField (MD (Fin.last bt)) (fun _=>1) 1=D^2 := by
    ext i j
    simp [MD,appendOne_aux,PositiveWeightRemoval.gramCoreField,Matrix.diagonal_one,pow_two]
  rw [he] at hg
  simpa only [appendOne_aux,D] using
    ((selectReduction basis (appendOne MD (D^2)) U (fun _=>1) (Fin.last (bt+1))).trans hg).trans
      (endpointAppendReduction basis M U (fun _=>1) old unary)

end PlanarHom.FixedRealEndpointGrams
