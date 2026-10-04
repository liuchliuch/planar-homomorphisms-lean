import PlanarHom.SupportBlockTractability

noncomputable section
open Classical
open scoped BigOperators
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.RootedRestriction PlanarHom.GraphComponentCode

private def isolate : MixedCode := ⟨1,[],[]⟩
private theorem isolate_valid : isolate.Valid 1 0 := by simp [isolate,Valid]
private theorem isolate_connected : (support isolate).Connected := by
  refine { preconnected := ?_, nonempty := ⟨⟨0,by decide⟩⟩ }
  intro u v
  have he : u=v := Subsingleton.elim (α := Fin 1) _ _
  subst v
  exact SimpleGraph.Reachable.refl _

-- One isolated vertex returns the exact sum of its background weights.
example {C : Type} [Fintype C] (M : Matrix C C ℚ) (w : C → ℚ) :
    isolate.evaluate isolate_valid (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w = ∑ c,w c := by
  have h := Fintype.sum_equiv (Equiv.funUnique (Fin 1) C)
    (GraphComponentCode.assignmentWeight isolate (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w)
    w (fun σ => by simp [GraphComponentCode.assignmentWeight,isolate,Equiv.funUnique,Equiv.piUnique])
  exact h

-- Zero matrix support retains every isolated color as a separate component.
example {C K : Type} [Fintype C] [Field K] :
    colorSupport (0 : Matrix C C K) (fun _ _ => rfl) = ⊥ := by
  ext i j
  simp [colorSupport]

-- The actual support-component sum on an isolated input gives exactly its
-- background-weight sum, even when every entry of the source matrix is zero.
example (w : Fin 3 → ℚ) :
    isolate.evaluate isolate_valid (fun _ : Fin 1 => (0 : Matrix (Fin 3) (Fin 3) ℚ))
      (fun u : Fin 0 => Fin.elim0 u) w =
    ∑ c : (colorSupport (0 : Matrix (Fin 3) (Fin 3) ℚ) (fun _ _ => rfl)).ConnectedComponent,
      isolate.evaluate isolate_valid
        (fun _ : Fin 1 => fun _ _ : c.supp => (0 : ℚ))
        (fun u : Fin 0 => Fin.elim0 u) (fun i : c.supp => w i.val) :=
  evaluate_eq_sum_supportBlocks isolate isolate_valid isolate_connected (by decide) _ _ w

-- Three input isolates are three computed queries and choose colors independently.
example : components ⟨3,[],[]⟩ = [isolate,isolate,isolate] := by decide
example : MixedCode.evaluate ⟨3,[],[]⟩ (by simp [Valid])
    (fun (_ : Fin 1) (_ _ : Fin 2) => (0 : ℚ))
    (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1) = 8 := by
  norm_num [evaluate]

-- Empty inputs make no calls and return one, including an empty color domain.
example {C K : Type} [Fintype C] [Field K] (M : Matrix C C K) (w : C → K) :
    MixedCode.evaluate ⟨0,[],[]⟩ (by simp [Valid]) (fun _ : Fin 1 => M)
      (fun u : Fin 0 => Fin.elim0 u) w = 1 := by
  rw [evaluate_components]
  have he : components ⟨0,[],[]⟩=[] := by decide
  simp only [he,List.map_nil,List.prod_nil]

-- In particular, the source with no colors has a constructed promised TM2
-- without any block evaluator premise: there are no support components.
example {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) (M : Matrix (Fin 0) (Fin 0) K) (w : Fin 0 → K) :
    (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w).InFP :=
  supportBlocks_inFP basis M (fun i => Fin.elim0 i) w (fun c => isEmptyElim c)

-- A negative off-diagonal entry is genuinely a support edge; a zero entry is not.
private def signedMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => if i=j then (if i=2 then -4 else 1) else if i<2 ∧ j<2 then -2 else 0
private theorem signedMatrix_symm : ∀ i j, signedMatrix i j=signedMatrix j i := by
  intro i j
  simp only [signedMatrix]
  by_cases he : i=j
  · subst j; rfl
  · simp [he,Ne.symm he,and_comm]

example : (colorSupport signedMatrix signedMatrix_symm).Adj 0 1 := by
  norm_num [colorSupport,signedMatrix,Fin.ext_iff,Fin.lt_def]
example : ¬(colorSupport signedMatrix signedMatrix_symm).Adj 0 2 := by
  norm_num [colorSupport,signedMatrix,Fin.ext_iff,Fin.lt_def]

private def repeatedLoop : MixedCode := ⟨1,[(0,0,0),(0,0,0)],[]⟩
private theorem repeatedLoop_valid : repeatedLoop.Valid 1 0 := by simp [repeatedLoop,Valid]
private theorem repeatedLoop_connected : (support repeatedLoop).Connected := by
  refine { preconnected := ?_, nonempty := ⟨⟨0,by decide⟩⟩ }
  intro u v
  have he : u=v := Subsingleton.elim (α := Fin 1) _ _
  subst v
  exact SimpleGraph.Reachable.refl _

-- Signs, loops and multiplicity all survive the support-block identity.
example : repeatedLoop.evaluate repeatedLoop_valid (fun _ : Fin 1 => signedMatrix)
    (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1) =
    ∑ c : (colorSupport signedMatrix signedMatrix_symm).ConnectedComponent,
      repeatedLoop.evaluate repeatedLoop_valid
        (fun _ : Fin 1 => fun i j : c.supp => signedMatrix i.val j.val)
        (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1) :=
  evaluate_eq_sum_supportBlocks repeatedLoop repeatedLoop_valid repeatedLoop_connected
    (by decide) signedMatrix signedMatrix_symm (fun _ => 1)

-- Signed diagonal blocks cancel even beside an isolated zero-row color.
private def cancelMatrix : Matrix (Fin 3) (Fin 3) ℚ := fun i j =>
  if i=j then (if i=0 then 1 else if i=1 then -1 else 0) else 0
private theorem cancelMatrix_symm : ∀ i j,cancelMatrix i j=cancelMatrix j i := by
  intro i j
  by_cases h:i=j
  · subst j; rfl
  · simp [cancelMatrix,h,Ne.symm h]
private def cancelGraph : MixedCode := ⟨1,[(0,0,0)],[]⟩
private theorem cancelGraph_valid : cancelGraph.Valid 1 0 := by simp [cancelGraph,Valid]
private theorem cancelGraph_value : cancelGraph.evaluate cancelGraph_valid (fun _ : Fin 1 => cancelMatrix)
    (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1) = 0 := by
  have h := Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3))
    (GraphComponentCode.assignmentWeight cancelGraph (fun _ : Fin 1 => cancelMatrix)
      (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1))
    (fun c : Fin 3 => cancelMatrix c c) (fun σ => by
      simp [GraphComponentCode.assignmentWeight,cancelGraph,binaryValue,Equiv.funUnique,Equiv.piUnique])
  change (∑ σ : Fin 1 → Fin 3, GraphComponentCode.assignmentWeight cancelGraph
    (fun _ : Fin 1 => cancelMatrix) (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1) σ)=0
  rw [h]
  norm_num [cancelMatrix,Fin.sum_univ_succ]
  decide
-- The all-zero row survives as a genuine singleton color component.
example : ((colorSupport cancelMatrix cancelMatrix_symm).connectedComponentMk 2).supp = {2} := by
  have hbot : colorSupport cancelMatrix cancelMatrix_symm=⊥ := by
    ext i j
    by_cases h : i=j <;> simp [colorSupport,cancelMatrix,h]
  ext c
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff,Set.mem_singleton_iff,
    SimpleGraph.ConnectedComponent.eq]
  rw [hbot,SimpleGraph.reachable_bot]

-- Exact cancellation is preserved when the connected partition is reconstructed
-- as the sum of literal numerical support blocks.
example :
    (∑ c : (colorSupport cancelMatrix cancelMatrix_symm).ConnectedComponent,
      cancelGraph.evaluate cancelGraph_valid
        (fun _ : Fin 1 => fun i j : c.supp => cancelMatrix i.val j.val)
        (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1)) = 0 := by
  have hc : (support cancelGraph).Connected := by
    refine { preconnected := ?_, nonempty := ⟨⟨0,by decide⟩⟩ }
    intro u v
    have he : u=v := Subsingleton.elim (α := Fin 1) _ _
    subst v
    exact SimpleGraph.Reachable.refl _
  rw [← evaluate_eq_sum_supportBlocks cancelGraph cancelGraph_valid hc (by decide)
    cancelMatrix cancelMatrix_symm (fun _ => 1)]
  exact cancelGraph_value

-- A zero row contributes zero when an edge occurrence is present.
example (j : Fin 3) : cancelMatrix 2 j=0 := by
  by_cases h : (2 : Fin 3)=j
  · subst j
    norm_num [cancelMatrix]
    decide
  · simp [cancelMatrix,h]

-- The promised machine API uses the unmodified raw word, even if a unary
-- header has a different bit pattern from the canonical encoding.
private def tailEncoding :=
  (((BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)).list).prod
    (BitEncoding.nat.prod BitEncoding.nat).list)
private def alternateIsolate : Bits := BitEncoding.frame [false] ++ tailEncoding.encode ([],[])
private theorem alternateIsolate_decode : encoding.decode alternateIsolate=some isolate := by
  change ((BitEncoding.unaryNat.prod tailEncoding).decode
    (BitEncoding.frame [false] ++ tailEncoding.encode ([],[]))).map
      (fun p => (⟨p.1,p.2.1,p.2.2⟩ : MixedCode)) = some isolate
  simp [BitEncoding.prod,BitEncoding.unaryNat,tailEncoding.decode_encode,isolate]
example : alternateIsolate ≠ encoding.encode isolate := by decide

example {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) (M : Matrix (Fin 2) (Fin 2) K) (w : Fin 2 → K)
    (h : (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w).InFP)
    (hp : isolate.PlanarValid 1 0) :
    Nonempty (Turing.TM2OutputsInTime h.computer.tm
      (alternateIsolate.map h.computer.inputAlphabet.symm)
      (some (((numberFieldEncoding basis).encode
        (isolate.evaluate isolate_valid (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w)).map
          h.computer.outputAlphabet.symm))
      (h.computer.time.eval alternateIsolate.length)) := by
  have ht := h.outputs alternateIsolate ⟨isolate,alternateIsolate_decode,hp⟩
  rw [show (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w).value
      alternateIsolate = _ from evaluationValue_decode basis _ _ _ alternateIsolate isolate
        alternateIsolate_decode isolate_valid] at ht
  exact ⟨ht⟩

#print axioms supportBlocks_inFP
#print axioms supportBlocks_inFP_of_connected
#print axioms restrictedEvaluation_inFP_iff
