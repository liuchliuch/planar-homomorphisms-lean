import PlanarHom.FixedRealJointInterpolation
import PlanarHom.FixedRealMixedPresentationTransport

/-! The full finite-joint A.3 endpoint with separately prescribed source and
target fields. The original source oracle is queried; arbitrary replies are
embedded by an actual program, and recovered target answers are descended. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealMixedInterpolation
open DensePolynomial Complexity FixedRealExtension RepresentedBit FiniteLanguageAliases ProductCompatibility
variable {d e c f s z q b u r v:ℕ} {K F S:Type} [Field K] [Field F] [Field S]
variable [Algebra (RationalFunction d) K] [Algebra (RationalFunction c) F] [Algebra (RationalFunction s) S]

def theoremA3_prescribed_joint
    (ambient:Module.Basis (Fin e) (RationalFunction d) K)
    (targetBasis:Module.Basis (Fin f) (RationalFunction c) F) (targetEmbed:F→+*K)
    (sourceBasis:Module.Basis (Fin z) (RationalFunction s) S) (sourceEmbed:S→+*K)
    (MS:Fin b→Matrix (Fin q) (Fin q) S) (US:Fin u→Fin q→S) (wS:Fin q→S)
    (MT:Fin b→Matrix (Fin q) (Fin q) F) (UT:Fin u→Fin q→F) (wT:Fin q→F)
    (N:Fin r→Matrix (Fin q) (Fin q) F) (V:Fin v→Fin q→F)
    (hM:∀l i j,targetEmbed (MT l i j)=sourceEmbed (MS l i j))
    (hU:∀l i,targetEmbed (UT l i)=sourceEmbed (US l i))
    (hw:∀i,targetEmbed (wT i)=sourceEmbed (wS i))
    (oldM:Fin r→Fin b) (oldU:Fin v→Fin u)
    (hzeroM:∀l i j,sourceEmbed (MS (oldM l) i j)=0→targetEmbed (N l i j)=0)
    (hprodM:∀l,HasProductMaps (fun p:Fin q×Fin q=>sourceEmbed (MS (oldM l) p.1 p.2))
      (fun p=>targetEmbed (N l p.1 p.2)))
    (hzeroU:∀l i,sourceEmbed (US (oldU l) i)=0→targetEmbed (V l i)=0)
    (hprodU:∀l,HasProductMaps (fun i=>sourceEmbed (US (oldU l) i)) (fun i=>targetEmbed (V l i)))
    (base:Problem) (available:Reduction (problem sourceBasis MS US wS) base) :
    Reduction (problem targetBasis (appendFamily MT N) (appendFamily UT V) wT) base := by
  let MC:=fun l i j=>sourceEmbed (MS l i j)
  let UC:=fun l i=>sourceEmbed (US l i)
  let wc:=fun i=>sourceEmbed (wS i)
  have rid:Reduction (problem ambient MC UC wc) (problem ambient MC UC wc):=
    queryReduction (presentation ambient) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
      (Complexity.MixedCode.PlanarValid b u) (Complexity.MixedCode.PlanarValid b u)
      (Complexity.MixedCode.totalEvaluation MC UC wc) (Complexity.MixedCode.totalEvaluation MC UC wc)
      id (fp_id _) (fun _ h=>h) (fun _ _=>rfl)
  have rc:=theoremA3_joint ambient MC UC wc (fun l i j=>targetEmbed (N l i j))
    (fun l i=>targetEmbed (V l i)) oldM oldU hzeroM hprodM hzeroU hprodU _ rid
  have hm:(fun l i j=>targetEmbed (appendFamily MT N l i j))=
      appendFamily MC (fun l i j=>targetEmbed (N l i j)) := by
    funext l i j
    refine Fin.addCases (fun a=>?_) (fun a=>?_) l
    · simpa only [appendFamily_old] using hM a i j
    · simp only [appendFamily_new]
  have hu:(fun l i=>targetEmbed (appendFamily UT V l i))=
      appendFamily UC (fun l i=>targetEmbed (V l i)) := by
    funext l i
    refine Fin.addCases (fun a=>?_) (fun a=>?_) l
    · simpa only [appendFamily_old] using hU a i
    · simp only [appendFamily_new]
  have hwt:(fun i=>targetEmbed (wT i))=wc:=funext hw
  have rc':Reduction
      (problem ambient (fun l i j=>targetEmbed (appendFamily MT N l i j))
        (fun l i=>targetEmbed (appendFamily UT V l i)) (fun i=>targetEmbed (wT i)))
      (problem ambient MC UC wc):=by
    simpa only [hm,hu,hwt] using rc
  exact (FixedRealMixedPresentationTransport.reduction ambient targetBasis targetEmbed sourceBasis sourceEmbed
    (appendFamily MT N) (appendFamily UT V) wT MS US wS rc').trans available

end PlanarHom.FixedRealMixedInterpolation
