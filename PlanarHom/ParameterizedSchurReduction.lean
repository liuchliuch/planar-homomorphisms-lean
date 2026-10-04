import PlanarHom.ParameterizedGraphReduction
import PlanarHom.MixedLabelExpansionReductions

/-! Uniform Schur multiplication by one fixed coexisting source label through
actual parallel occurrence expansion. The original parameter is unchanged. -/
noncomputable section
namespace PlanarHom.ParameterizedSchurReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases PairProjectionMachines FiniteLabelWordLookupMachines
variable {X K : Type} [Field K] [Algebra ℚ K] {dimension q b u : ℕ}

def words (old : Fin b) : Fin (b+1)→List (Fin (b+1)) :=
  Fin.lastCases [old.castSucc,Fin.last b] (fun i=>[i.castSucc])

theorem wordMatrices_eq (M : Fin b→Matrix (Fin q) (Fin q) K)
    (A : Matrix (Fin q) (Fin q) K) (old : Fin b) :
    wordMatrices (words old) (appendOne M A)=appendOne M (fun i j=>M old i j*A i j) := by
  funext l i j
  refine Fin.lastCases ?_ (fun k=>?_) l
  · simp only [wordMatrices,words,Fin.lastCases_last,List.map_cons,List.map_nil,List.prod_cons,
      List.prod_nil,mul_one,appendOne_aux]
    change appendOne M A (Fin.castAdd 1 old) i j*A i j=M old i j*A i j
    rw [appendOne_old]
  · simp only [wordMatrices,words,Fin.lastCases_castSucc,List.map_cons,List.map_nil,List.prod_cons,
      List.prod_nil,mul_one]
    change appendOne M A (Fin.castAdd 1 k) i j=appendOne M (fun i j=>M old i j*A i j) (Fin.castAdd 1 k) i j
    rw [appendOne_old,appendOne_old]

def reduction (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K) (w : Fin q→K)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop) (old : Fin b)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis ex M U w F allowed) base) :
    PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis ex M U w (fun x i j=>M old i j*F x i j) allowed)
      (ParameterizedMatrixEvaluation.problem basis ex M U w F allowed) := by
  let ep:=ex.prod encoding
  let prepare : X×MixedCode→Bits×List (X×MixedCode) := fun p=>([],[(p.1,p.2.expandBinaryWords (finTable (words old)))])
  let recover : Bits×List K→K := fun p=>p.2.sum
  have hp : FP ep (BitEncoding.bits.prod ep.list) prepare := by
    have query := (fp_fst ex encoding).pair ((fp_snd ex encoding).comp (fp_expandBinaryWords (finTable (words old))))
    have singleton := (query.pair (fp_const ep ep.list [])).comp (ListMutationMachines.fp_cons ep)
    exact (fp_const ep BitEncoding.bits []).pair singleton
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp (MaterializedFieldListMachines.fp_sum basis)
  apply ParameterizedGraphReduction.reductionOfPipeline basis ex ex BitEncoding.bits
    M U w M U w (fun x i j=>M old i j*F x i j) F allowed allowed prepare recover hp hr ?_ ?_ base simulation
  · intro p ha hg query hq
    obtain rfl:=List.mem_singleton.mp hq
    exact ⟨ha,expandBinaryWords_planar _ hg (lookup_finTable_lt (words old))⟩
  · intro p ha hg
    have hv:=expandBinaryWords_valid (finTable (words old)) hg.1 (lookup_finTable_lt (words old))
    simp only [prepare,recover,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      ParameterizedMatrixEvaluation.answer,totalEvaluation_valid _ _ _ _ hg.1,
      totalEvaluation_valid _ _ _ _ hv]
    rw [evaluate_expandBinaryWords,wordMatrices_eq]

end PlanarHom.ParameterizedSchurReduction
