import PlanarHom.ParameterizedSchurReduction

/-! The fixed factor may be an auxiliary available label; the target retains
all original labels and appends only the requested parameterized Schur product. -/
noncomputable section
namespace PlanarHom.ParameterizedAppendSchurReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases PairProjectionMachines FiniteLabelWordLookupMachines
variable {X K : Type} [Field K] [Algebra ℚ K] {dimension q b u : ℕ}

def words (b : ℕ) : Fin (b+1)→List (Fin ((b+1)+1)) :=
  Fin.lastCases [(Fin.last b).castSucc,Fin.last (b+1)] (fun i=>[i.castSucc.castSucc])

theorem wordMatrices_eq (M : Fin b→Matrix (Fin q) (Fin q) K)
    (A F : Matrix (Fin q) (Fin q) K) :
    wordMatrices (words b) (appendOne (appendOne M A) F)=appendOne M (fun i j=>A i j*F i j) := by
  funext l i j
  refine Fin.lastCases ?_ (fun k=>?_) l
  · simp only [wordMatrices,words,Fin.lastCases_last,List.map_cons,List.map_nil,List.prod_cons,
      List.prod_nil,mul_one,appendOne_aux]
    change appendOne (appendOne M A) F (Fin.castAdd 1 (Fin.last b)) i j*F i j=A i j*F i j
    rw [appendOne_old,appendOne_aux]
  · simp only [wordMatrices,words,Fin.lastCases_castSucc,List.map_cons,List.map_nil,List.prod_cons,
      List.prod_nil,mul_one]
    change appendOne (appendOne M A) F (Fin.castAdd 1 (Fin.castAdd 1 k)) i j=
      appendOne M (fun i j=>A i j*F i j) (Fin.castAdd 1 k) i j
    rw [appendOne_old,appendOne_old,appendOne_old]

def reduction (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (A : Matrix (Fin q) (Fin q) K)
    (U : Fin u→Fin q→K) (w : Fin q→K)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis ex (appendOne M A) U w F allowed) base) :
    PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis ex M U w (fun x i j=>A i j*F x i j) allowed)
      (ParameterizedMatrixEvaluation.problem basis ex (appendOne M A) U w F allowed) := by
  let ep:=ex.prod encoding
  let prepare : X×MixedCode→Bits×List (X×MixedCode) := fun p=>([],[(p.1,p.2.expandBinaryWords (finTable (words b)))])
  let recover : Bits×List K→K := fun p=>p.2.sum
  have hp : FP ep (BitEncoding.bits.prod ep.list) prepare := by
    have query := (fp_fst ex encoding).pair ((fp_snd ex encoding).comp (fp_expandBinaryWords (finTable (words b))))
    have singleton := (query.pair (fp_const ep ep.list [])).comp (ListMutationMachines.fp_cons ep)
    exact (fp_const ep BitEncoding.bits []).pair singleton
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp (MaterializedFieldListMachines.fp_sum basis)
  apply ParameterizedGraphReduction.reductionOfPipeline basis ex ex BitEncoding.bits
    M U w (appendOne M A) U w (fun x i j=>A i j*F x i j) F allowed allowed prepare recover hp hr ?_ ?_ base simulation
  · intro p ha hg query hq
    obtain rfl:=List.mem_singleton.mp hq
    exact ⟨ha,expandBinaryWords_planar _ hg (lookup_finTable_lt (words b))⟩
  · intro p ha hg
    have hv:=expandBinaryWords_valid (finTable (words b)) hg.1 (lookup_finTable_lt (words b))
    simp only [prepare,recover,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      ParameterizedMatrixEvaluation.answer,totalEvaluation_valid _ _ _ _ hg.1,
      totalEvaluation_valid _ _ _ _ hv]
    rw [evaluate_expandBinaryWords,wordMatrices_eq]

end PlanarHom.ParameterizedAppendSchurReduction
