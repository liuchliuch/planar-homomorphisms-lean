import PlanarHom.GraphNonadaptiveReduction
import PlanarHom.MixedRelabelSemantics
import PlanarHom.MaterializedFieldListMachines

/-! Actual finite-label alias reductions between raw planar mixed languages.
This is the computational bridge for duplicate/auxiliary labels in joint
availability, rather than a free identification of equal-valued constraints. -/
namespace PlanarHom.Complexity.MixedCode
noncomputable section
open PlanarHom.FiniteLabelLookupMachines
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension a b u : ℕ}

noncomputable def binaryRelabelReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : Fin a→Fin b) (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (M ∘ ρ) U w)
      (evaluationProblem basis M U w):=by
  let prepare : MixedCode→Bits × List MixedCode:=fun g=>([],[g.relabelBinary (finTable ρ)])
  let recover : Bits × List K→K:=fun p=>p.2.sum
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare:=by
    have hs:=((fp_relabelBinary (finTable ρ)).pair (fp_const encoding encoding.list [])).comp
      (PlanarHom.ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hs
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover:=
    (PairProjectionMachines.fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp
      (PlanarHom.MaterializedFieldListMachines.fp_sum basis)
  apply planarReductionOfPipeline basis BitEncoding.bits (M ∘ ρ) U w M U w prepare recover hp hr
  · intro g hg query hq
    have he:query=g.relabelBinary (finTable ρ):=List.mem_singleton.mp hq
    subst query
    exact relabelBinary_planar _ hg (lookup_finTable_lt ρ)
  · intro g hg
    have hv: (g.relabelBinary (finTable ρ)).Valid b u:=relabelBinary_valid _ hg.1 (lookup_finTable_lt ρ)
    change [totalEvaluation M U w (g.relabelBinary (finTable ρ))].sum=g.evaluate hg.1 (M ∘ ρ) U w
    simpa only [List.sum_cons,List.sum_nil,add_zero,totalEvaluation_valid M U w _ hv] using
      evaluate_relabelBinary g hg.1 ρ M U w

noncomputable def unaryRelabelReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : Fin a→Fin u) (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M (U ∘ ρ) w)
      (evaluationProblem basis M U w):=by
  let prepare : MixedCode→Bits × List MixedCode:=fun g=>([],[g.relabelUnary (finTable ρ)])
  let recover : Bits × List K→K:=fun p=>p.2.sum
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare:=by
    have hs:=((fp_relabelUnary (finTable ρ)).pair (fp_const encoding encoding.list [])).comp
      (PlanarHom.ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hs
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover:=
    (PairProjectionMachines.fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp
      (PlanarHom.MaterializedFieldListMachines.fp_sum basis)
  apply planarReductionOfPipeline basis BitEncoding.bits M (U ∘ ρ) w M U w prepare recover hp hr
  · intro g hg query hq
    have he:query=g.relabelUnary (finTable ρ):=List.mem_singleton.mp hq
    subst query
    exact relabelUnary_planar _ hg (lookup_finTable_lt ρ)
  · intro g hg
    have hv: (g.relabelUnary (finTable ρ)).Valid b u:=relabelUnary_valid _ hg.1 (lookup_finTable_lt ρ)
    change [totalEvaluation M U w (g.relabelUnary (finTable ρ))].sum=g.evaluate hg.1 M (U ∘ ρ) w
    simpa only [List.sum_cons,List.sum_nil,add_zero,totalEvaluation_valid M U w _ hv] using
      evaluate_relabelUnary g hg.1 ρ M U w

end
end PlanarHom.Complexity.MixedCode
