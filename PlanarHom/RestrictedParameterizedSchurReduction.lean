import PlanarHom.ParameterizedAppendSchurReduction
import PlanarHom.RestrictedParameterizedGraphReduction

noncomputable section
namespace PlanarHom.RestrictedParameterizedSchurReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases PairProjectionMachines FiniteLabelWordLookupMachines
open ParameterizedAppendSchurReduction
variable {X K : Type} [Field K] [Algebra ℚ K] {dimension q b u : ℕ}

def reduction (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (A : Matrix (Fin q) (Fin q) K)
    (U : Fin u→Fin q→K) (w : Fin q→K)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop)
    (HT HS : MixedCode→Prop) (hvalid : ∀g,HT g→g.Valid (b+1) u)
    (hmap : ∀g,HT g→HS (g.expandBinaryWords (finTable (words b))))
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (RestrictedMatrixFamilyReduction.targetProblem basis ex (appendOne M A) U w F allowed HS) base) :
    PromisePolyTimeTuringReduction
      (RestrictedMatrixFamilyReduction.targetProblem basis ex M U w (fun x i j=>A i j*F x i j) allowed HT)
      (RestrictedMatrixFamilyReduction.targetProblem basis ex (appendOne M A) U w F allowed HS) := by
  let ep:=ex.prod encoding
  let prepare : X×MixedCode→Bits×List (X×MixedCode) := fun p=>([],[(p.1,p.2.expandBinaryWords (finTable (words b)))])
  let recover : Bits×List K→K := fun p=>p.2.sum
  have hp : FP ep (BitEncoding.bits.prod ep.list) prepare := by
    have query := (fp_fst ex encoding).pair ((fp_snd ex encoding).comp (fp_expandBinaryWords (finTable (words b))))
    have singleton := (query.pair (fp_const ep ep.list [])).comp (ListMutationMachines.fp_cons ep)
    exact (fp_const ep BitEncoding.bits []).pair singleton
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp (MaterializedFieldListMachines.fp_sum basis)
  apply RestrictedParameterizedGraphReduction.reductionOfPipeline basis ex ex BitEncoding.bits
    M U w (appendOne M A) U w (fun x i j=>A i j*F x i j) F allowed allowed HT HS prepare recover hp hr ?_ ?_ base simulation
  · intro p ha hg query hq
    obtain rfl:=List.mem_singleton.mp hq
    exact ⟨ha,hmap _ hg⟩
  · intro p ha hg
    have hv:=expandBinaryWords_valid (finTable (words b)) (hvalid _ hg) (lookup_finTable_lt (words b))
    simp only [prepare,recover,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      ParameterizedMatrixEvaluation.answer,totalEvaluation_valid _ _ _ _ (hvalid _ hg),
      totalEvaluation_valid _ _ _ _ hv]
    rw [evaluate_expandBinaryWords,wordMatrices_eq]

end PlanarHom.RestrictedParameterizedSchurReduction
