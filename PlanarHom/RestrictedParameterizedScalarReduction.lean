import PlanarHom.RestrictedParameterizedGraphReduction
import PlanarHom.SelectedScalarSemantics
import PlanarHom.FixedPowerMachines
import PlanarHom.UnaryMarkedCount
import PlanarHom.MaterializedFieldListMachines

/-! A fixed scalar on the runtime matrix is removed by an actual occurrence
count, fixed-field exponentiation and post-oracle multiplication. -/
noncomputable section
namespace PlanarHom.RestrictedParameterizedScalarReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases PairProjectionMachines
variable {X K : Type} [Field K] [Algebra ℚ K] {dimension q b u : ℕ}

def reduction (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K) (w : Fin q→K)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop) (c : K)
    (H : MixedCode→Prop) (hvalid : ∀g,H g→g.Valid (b+1) u)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (RestrictedMatrixFamilyReduction.targetProblem basis ex M U w F allowed H) base) :
    PromisePolyTimeTuringReduction
      (RestrictedMatrixFamilyReduction.targetProblem basis ex M U w (fun x=>c • F x) allowed H)
      (RestrictedMatrixFamilyReduction.targetProblem basis ex M U w F allowed H) := by
  let ep:=ex.prod encoding
  let ef:=numberFieldEncoding basis
  let prepare : X×MixedCode→ℕ×List (X×MixedCode) := fun p=>(p.2.markedCount b,[p])
  let recover : ℕ×List K→K := fun p=>c^p.1*p.2.sum
  have hp : FP ep (BitEncoding.unaryNat.prod ep.list) prepare := by
    have count := (fp_snd ex encoding).comp (fp_unaryMarkedCount b)
    have singleton := ((fp_id ep).pair (fp_const ep ep.list [])).comp (ListMutationMachines.fp_cons ep)
    exact count.pair singleton
  have hr : FP (BitEncoding.unaryNat.prod ef.list) ef recover :=
    (((fp_fst BitEncoding.unaryNat ef.list).comp (FixedPowerMachines.fp_power basis c)).pair
      ((fp_snd BitEncoding.unaryNat ef.list).comp (MaterializedFieldListMachines.fp_sum basis))).comp
        (FixedFieldArithmetic.fp_multiplication basis)
  apply RestrictedParameterizedGraphReduction.reductionOfPipeline basis ex ex BitEncoding.unaryNat
    M U w M U w (fun x=>c • F x) F allowed allowed H H prepare recover hp hr
    (fun p ha hg query hq=>by obtain rfl:=List.mem_singleton.mp hq; exact ⟨ha,hg⟩)
    ?_ base simulation
  intro p ha hg
  simp only [prepare,recover,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  simp only [ParameterizedMatrixEvaluation.answer,totalEvaluation_valid _ _ _ _ (hvalid _ hg)]
  exact (SelectedScalarSemantics.evaluate_append_smul p.2 (hvalid _ hg) M (F p.1) U w c).symm

end PlanarHom.RestrictedParameterizedScalarReduction
