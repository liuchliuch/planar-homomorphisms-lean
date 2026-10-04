import PlanarHom.RankOneEvaluationMachine

noncomputable section
open Classical
open scoped BigOperators
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.GraphDegreeMachines

private def multigraph : MixedCode := ⟨3,[(0,0,0),(0,1,0),(0,1,0)],[]⟩
example : degrees multigraph=[0,2,4] := by decide
example : degrees ⟨0,[],[]⟩=[] := by decide
example : degrees ⟨3,[],[]⟩=[0,0,0] := by decide
example : degrees ⟨1,[(0,0,0),(0,0,0)],[]⟩=[4] := by decide

example : RankOneEvaluationMachine.evaluate (![2,-1] : Fin 2→ℚ) ![3,5] multigraph=7208 := by
  change ([0,2,4].map (RankOneEvaluationMachine.factor (![2,-1] : Fin 2→ℚ) ![3,5])).prod=7208
  norm_num [RankOneEvaluationMachine.factor,Fin.sum_univ_two]
example : RankOneEvaluationMachine.evaluate (![1,-1] : Fin 2→ℚ) (fun _=>1)
    ⟨2,[(0,1,0)],[]⟩=0 := by
  change ([1,1].map (RankOneEvaluationMachine.factor (![1,-1] : Fin 2→ℚ) (fun _=>1))).prod=0
  norm_num [RankOneEvaluationMachine.factor,Fin.sum_univ_two]
example : RankOneEvaluationMachine.evaluate (fun _ : Fin 1=>(3 : ℚ)) (fun _=>2)
    ⟨2,[(0,0,0)],[]⟩=36 := by
  change ([0,2].map (RankOneEvaluationMachine.factor (fun _ : Fin 1=>(3 : ℚ)) (fun _=>2))).prod=36
  norm_num [RankOneEvaluationMachine.factor,Fin.sum_univ_succ]

example {K : Type} [Field K] (a w : Fin 0→K) : RankOneEvaluationMachine.evaluate a w ⟨0,[],[]⟩=1 := by
  simp [RankOneEvaluationMachine.evaluate,degrees]
example {K : Type} [Field K] (a w : Fin 0→K) : RankOneEvaluationMachine.evaluate a w ⟨1,[],[]⟩=0 := by
  simp [RankOneEvaluationMachine.evaluate,RankOneEvaluationMachine.factor,degrees,degree,endpoints]

example {K : Type} [Field K] [Algebra ℚ K] {d : ℕ} (basis : Module.Basis (Fin d) ℚ K)
    (a w : Fin 0→K) :
    (evaluationProblem basis (fun _ : Fin 1=>fun i j=>a i*a j) (fun u : Fin 0=>Fin.elim0 u) w).InFP :=
  RankOneEvaluationMachine.evaluation_inFP basis a w

-- Unary vertex headers need not use the canonical all-true word. The complete
-- machine consumes this raw word and returns the isolate's exact weight sum.
private def rawIsolate : Bits := [true,false,false,true,false,false,false]
private def isolate : MixedCode := ⟨1,[],[]⟩
private theorem rawIsolate_decode : encoding.decode rawIsolate=some isolate := by decide
private theorem isolate_valid : isolate.Valid 1 0 := by simp [isolate,Valid]
example {K : Type} [Field K] [Algebra ℚ K] {q d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) (a w : Fin q→K) :
    let h := RankOneEvaluationMachine.validEvaluation_inFP basis a w
    Nonempty (Turing.TM2OutputsInTime h.computer.tm (rawIsolate.map h.computer.inputAlphabet.symm)
      (some (((numberFieldEncoding basis).encode (∑i,w i)).map h.computer.outputAlphabet.symm))
      (h.computer.time.eval rawIsolate.length)) := by
  dsimp only
  let h := RankOneEvaluationMachine.validEvaluation_inFP basis a w
  have hp : (restrictedEvaluationProblem basis (fun _ : Fin 1=>fun i j=>a i*a j)
      (fun u : Fin 0=>Fin.elim0 u) w (Valid 1 0)).valid rawIsolate :=
    ⟨isolate,rawIsolate_decode,isolate_valid⟩
  have ht := h.outputs rawIsolate hp
  have he : isolate.evaluate isolate_valid (fun _ : Fin 1=>fun i j=>a i*a j)
      (fun u : Fin 0=>Fin.elim0 u) w=∑i,w i := by
    rw [rankOne_evaluate]
    simp [degrees,degree,endpoints,isolate]
  change Nonempty (Turing.TM2OutputsInTime h.computer.tm _ _ _)
  change Turing.TM2OutputsInTime h.computer.tm _
    (some ((evaluationValue basis (fun _ : Fin 1=>fun i j=>a i*a j)
      (fun u : Fin 0=>Fin.elim0 u) w rawIsolate).map h.computer.outputAlphabet.symm)) _ at ht
  rw [evaluationValue_decode basis _ _ _ rawIsolate isolate rawIsolate_decode isolate_valid,he] at ht
  exact ⟨ht⟩

#print axioms RankOneEvaluationMachine.fp_evaluate
#print axioms RankOneEvaluationMachine.evaluation_inFP
