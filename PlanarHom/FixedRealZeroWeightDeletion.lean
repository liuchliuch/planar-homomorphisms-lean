import PlanarHom.FixedRealComponentReduction
import PlanarHom.FixedRealPresentationReductions
import PlanarHom.RepresentedQueryReduction
import PlanarHom.ZeroWeightSourceReduction
import PlanarHom.NatListSumMachines

/-! NEW: exact zero-weight deletion in the represented fixed-real model.
The oracle query preserves the original graph. Every actual color with nonzero
weight is retained, including the empty-source boundary. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealZeroWeights
open DensePolynomial Complexity Complexity.MixedCode RepresentedBit PairProjectionMachines
variable {d e b u : ℕ} {K C D : Type} [Field K] [Algebra (RationalFunction d) K]
  [Fintype C] [Fintype D]
variable (basis : Module.Basis (Fin e) (RationalFunction d) K)

def sameGraphReduction
    (MT : Fin b → Matrix C C K) (UT : Fin u → C → K) (wT : C → K)
    (MS : Fin b → Matrix D D K) (US : Fin u → D → K) (wS : D → K)
    (he : ∀ g : MixedCode, ∀ hg : g.Valid b u,
      g.evaluate hg MS US wS = g.evaluate hg MT UT wT) :
    Reduction (FixedRealComponents.problem basis MT UT wT) (FixedRealComponents.problem basis MS US wS) := by
  apply queryReduction (FixedRealExtension.presentation basis) MixedCode.encoding MixedCode.encoding
    MixedCode.normalizer (PlanarValid b u) (PlanarValid b u)
    (totalEvaluation MT UT wT) (totalEvaluation MS US wS) id (fp_id _) (fun _ h => h)
  intro g hg
  simp only [id_eq,totalEvaluation_valid _ _ _ g hg.1]
  exact he g hg.1

def deleteReduction (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (S : C → Prop) [Fintype {i // S i}] (hz : ∀ i, ¬S i → w i = 0) :
    Reduction (FixedRealComponents.problem basis M U w)
      (FixedRealComponents.problem basis (fun l (i j : {i // S i}) => M l i.val j.val)
        (fun l (i : {i // S i}) => U l i.val) (fun i => w i.val)) :=
  sameGraphReduction basis M U w _ _ _
    (fun g hg => (evaluate_restrict_zero_weights g hg M U w S hz).symm)

def restoreReduction (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (S : C → Prop) [Fintype {i // S i}] (hz : ∀ i, ¬S i → w i = 0) :
    Reduction (FixedRealComponents.problem basis (fun l (i j : {i // S i}) => M l i.val j.val)
        (fun l (i : {i // S i}) => U l i.val) (fun i => w i.val))
      (FixedRealComponents.problem basis M U w) :=
  sameGraphReduction basis _ _ _ M U w
    (fun g hg => evaluate_restrict_zero_weights g hg M U w S hz)

def emptyAnswer (g : MixedCode) : FixedRealExtension.Code d e :=
  if g.vertices = 0 then (FixedRealExtension.presentation basis).constant 1
  else (FixedRealExtension.presentation basis).constant 0

theorem fp_emptyAnswer : FP MixedCode.encoding (FixedRealExtension.encoding d e) (emptyAnswer basis) := by
  have hn := MixedCode.fp_vertices.comp UnaryNatConversionMachine.fp_conversion
  have hz := (hn.pair (fp_const MixedCode.encoding BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  exact hz.ite (fp_const _ _ ((FixedRealExtension.presentation basis).constant 1))
    (fp_const _ _ ((FixedRealExtension.presentation basis).constant 0))

theorem zero_background_inFP (M : Fin b → Matrix C C K) (U : Fin u → C → K) :
    (FixedRealComponents.problem basis M U (fun _ => 0)).InFP := by
  apply (FixedRealExtension.presentation basis).problem_inFP MixedCode.encoding MixedCode.normalizer _ _
    (emptyAnswer basis) (fp_emptyAnswer basis)
  · intro g hg
    unfold emptyAnswer
    split <;> exact (FixedRealExtension.presentation basis).constant_valid _
  · intro g hg
    rw [totalEvaluation_valid _ _ _ g hg.1,evaluate_zero_background]
    unfold emptyAnswer
    split <;> simp_all only [Presentation.constant_value,ite_true,ite_false]

end PlanarHom.FixedRealZeroWeights
