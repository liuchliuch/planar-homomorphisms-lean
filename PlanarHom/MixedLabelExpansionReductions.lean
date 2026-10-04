import PlanarHom.MixedLabelExpansionSemantics
import PlanarHom.PrescribedDomainWordExpansion
import PlanarHom.GraphNonadaptiveReduction
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.PromiseReductionTransport

/-! Actual single-query parallel product reductions, on all successfully decoded
raw planar inputs and on the exact prescribed-domain promise. -/
namespace PlanarHom.Complexity.MixedCode
noncomputable section
open PlanarHom.FiniteLabelWordLookupMachines PlanarHom.PrescribedDomains
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension a b u d : ℕ}

def wordExpansionPrepare (ρ : Fin a→List (Fin b)) (g : MixedCode) : Bits×List MixedCode :=
  ([],[g.expandBinaryWords (finTable ρ)])

theorem wordExpansionPrepare_single_query (ρ : Fin a→List (Fin b)) (g : MixedCode) :
    (wordExpansionPrepare ρ g).2.length=1 := rfl

theorem fp_wordExpansionPrepare (ρ : Fin a→List (Fin b)) :
    FP encoding (BitEncoding.bits.prod encoding.list) (wordExpansionPrepare ρ) := by
  have hq := ((fp_expandBinaryWords (finTable ρ)).pair (fp_const encoding encoding.list [])).comp
    (PlanarHom.ListMutationMachines.fp_cons encoding)
  exact (fp_const encoding BitEncoding.bits []).pair hq

noncomputable def binaryWordExpansionReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : Fin a→List (Fin b)) (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (wordMatrices ρ M) U w)
      (evaluationProblem basis M U w) := by
  let recover : Bits×List K→K := fun p => p.2.sum
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (PairProjectionMachines.fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp
      (PlanarHom.MaterializedFieldListMachines.fp_sum basis)
  apply planarReductionOfPipeline basis BitEncoding.bits (wordMatrices ρ M) U w M U w
    (wordExpansionPrepare ρ) recover (fp_wordExpansionPrepare ρ) hr
  · intro g hg query hq
    have he : query=g.expandBinaryWords (finTable ρ) := List.mem_singleton.mp hq
    subst query
    exact expandBinaryWords_planar _ hg (lookup_finTable_lt ρ)
  · intro g hg
    have hv := expandBinaryWords_valid (finTable ρ) hg.1 (lookup_finTable_lt ρ)
    change [totalEvaluation M U w (g.expandBinaryWords (finTable ρ))].sum=
      g.evaluate hg.1 (wordMatrices ρ M) U w
    simpa only [List.sum_cons,List.sum_nil,add_zero,totalEvaluation_valid M U w _ hv] using
      evaluate_expandBinaryWords g hg.1 ρ M U w

noncomputable def domainBinaryWordExpansionReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : Fin a→List (Fin b)) (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K) (D : Fin d→Set C)
    (BT : Fin a→Fin d→Fin d→Prop) (BS : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (hB : ∀i x y,BT i x y→∀j∈ρ i,BS j x y) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis (wordMatrices ρ M) U w D BT T)
      (domainEvaluationProblem basis M U w D BS T) := by
  let recover : Bits×List K→K := fun p => p.2.sum
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (PairProjectionMachines.fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp
      (PlanarHom.MaterializedFieldListMachines.fp_sum basis)
  have hqueries : ∀g,EncodedGraph BT T g→∀query∈(wordExpansionPrepare ρ g).2,EncodedGraph BS T query := by
    intro g hg query hq
    have he : query=g.expandBinaryWords (finTable ρ) := List.mem_singleton.mp hq
    subst query
    exact hg.expandBinaryWords ρ hB
  have hcorrect : ∀g (hg : EncodedGraph BT T g),
      recover ((wordExpansionPrepare ρ g).1,
        (wordExpansionPrepare ρ g).2.map (totalEvaluation M (extendedUnaries U D) w))=
      g.evaluate (hg.planarValid BT T).1 (wordMatrices ρ M) (extendedUnaries U D) w := by
    intro g hg
    have hv := (hg.planarValid BT T).1
    have hv' := expandBinaryWords_valid (finTable ρ) hv (lookup_finTable_lt ρ)
    change [totalEvaluation M (extendedUnaries U D) w (g.expandBinaryWords (finTable ρ))].sum=
      g.evaluate hv (wordMatrices ρ M) (extendedUnaries U D) w
    simpa only [List.sum_cons,List.sum_nil,add_zero,totalEvaluation_valid M (extendedUnaries U D) w _ hv'] using
      evaluate_expandBinaryWords g hv ρ M (extendedUnaries U D) w
  let r := reductionOfPipeline basis BitEncoding.bits (wordMatrices ρ M) (extendedUnaries U D) w
    M (extendedUnaries U D) w (EncodedGraph BT T) (EncodedGraph BS T)
    (fun _ h => (h.planarValid BT T).1) (fun _ h => (h.planarValid BS T).1)
    (wordExpansionPrepare ρ) recover (fp_wordExpansionPrepare ρ) hr hqueries hcorrect
  exact r.transport _ _
    (fun raw h => (encodedInput_iff_graph BT T raw).mp h)
    (fun raw h => (encodedInput_iff_graph BS T raw).mpr h)
    (fun _ _ => rfl) (fun _ _ => rfl)

end
end PlanarHom.Complexity.MixedCode
