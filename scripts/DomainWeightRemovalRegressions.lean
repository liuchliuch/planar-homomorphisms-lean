import PlanarHom.PositiveWeightSourceAvailability

noncomputable section
open Classical
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.PositiveWeightRemoval PlanarHom.PrescribedDomains
open PlanarHom.AlgebraicProductInterpolation

private def domains : Fin 2→Set (Fin 2) := fun d=>if d=0 then {0} else Set.univ
private def policy : Fin 2→Fin 2→Fin 2→Prop := fun l x y=>if l=0 then True else x=0 ∧ y=0
private def typing : Fin 2→Fin 2→Prop := fun l x=>if l=0 then x=0 else True

-- A narrow old vertex domain is retained; the full domain is only used by
-- private path vertices. A companion label is not silently made global.
example : domains 0≠domains 1 := by
  intro h
  have hi : (1 : Fin 2)∈domains 1 := by simp [domains]
  rw [←h] at hi
  simp [domains] at hi
example : policy 0 0 1 := by simp [policy]
example : ¬policy 1 1 0 := by simp [policy]
example : withGlobalMatrix policy 0 1 1 0↔policy 1 1 0 := by
  simp [withGlobalMatrix]
example : PathDomainTyping policy 0 1 0 0 := by simp [PathDomainTyping,policy]

private def original : MixedCode := ⟨2,[(0,0,0),(0,1,0)],[(0,2),(0,2),(0,0)]⟩
private theorem original_valid : original.Valid 2 3 := by simp [original,Valid]
private def assignment : Fin 2→Fin 2 := ![0,1]

-- Two new unary occurrences become two loops. The old unary stays at0;
-- intrinsic domain labels3,4 are restored to2,3 without changing δ.
example : domainUnaryLoopTransform 2 2 0 (withDomains (unaryTypes:=3) original assignment) =
    ⟨2,[(0,0,0),(0,1,0),(0,0,0),(0,0,0)],[(0,0),(0,2),(1,3)]⟩ := by decide
example : domainUnaryLoopTransform 2 2 0 (withDomains (unaryTypes:=3) original assignment) =
    withDomains (unaryTypes:=2) (realizeUnaryLoops 2 0 original) assignment :=
  domainUnaryLoopTransform_withDomains original original_valid assignment 0
example : (withDomains (unaryTypes:=3) original assignment).addLoops 0 =
    withDomains (unaryTypes:=3) (original.addLoops 0) assignment := rfl

-- No unary occurrences and no vertices require no loop and no domain record.
example : domainUnaryLoopTransform 0 2 0 ⟨0,[],[]⟩=⟨0,[],[]⟩ := by decide

-- A valid alternate raw label word[false] denotes2. Normalization occurs
-- before the actual finite label permutation and loop compiler.
-- The literal bytes below encode one vertex, no edges, unary label2 using
-- [false], and the target domain0 record at label3.
private def rawDomainGraph : Bits :=
  [true,true,false,true,false,false,true,false,true,true,false,true,false,true,false,false,true,false,true,true,true,true,false]
private def decodedDomainGraph : MixedCode := ⟨1,[],[(0,2),(0,3)]⟩
private theorem rawDomainGraph_decode : encoding.decode rawDomainGraph=some decodedDomainGraph := by decide
#guard rawDomainGraph != encoding.encode decodedDomainGraph
example : domainUnaryLoopTransform 2 2 0 decodedDomainGraph=⟨1,[(0,0,0)],[(0,2)]⟩ := by decide
example : encoding.decode [true]=none := by decide
example : ¬(⟨1,[],[(1,2)]⟩ : MixedCode).Valid 1 5 := by simp [Valid]

private def rawLoopComputer := MachineComposition.composeComputers normalizer
  (Classical.choice (fp_domainUnaryLoopTransform 2 2 0))
example : Nonempty (Turing.TM2OutputsInTime rawLoopComputer.tm
    (rawDomainGraph.map rawLoopComputer.inputAlphabet.symm)
    (some ((encoding.encode (⟨1,[(0,0,0)],[(0,2)]⟩ : MixedCode)).map rawLoopComputer.outputAlphabet.symm))
    (rawLoopComputer.time.eval rawDomainGraph.length)) := by
  let x : BitEncoding.ValidWord encoding := ⟨rawDomainGraph,⟨decodedDomainGraph,rawDomainGraph_decode⟩⟩
  have hv : x.value=decodedDomainGraph := BitEncoding.ValidWord.value_eq rawDomainGraph_decode
  have h := rawLoopComputer.outputsFun x
  have ho : domainUnaryLoopTransform 2 2 0 decodedDomainGraph=⟨1,[(0,0,0)],[(0,2)]⟩ := by decide
  exact ⟨by simpa only [BitEncoding.toFinEncoding,BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw,Function.comp_apply,hv,ho] using h⟩

-- Instantiate every main row hypothesis with a genuinely signed matrix.
private def signedMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1,-2;-2,5]
private theorem signed_symm : ∀i j,signedMatrix i j=signedMatrix j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [signedMatrix]
private theorem signed_nonzero : ∀i,signedMatrix i≠0 := by
  intro i h
  have h0 := congrFun h 0
  fin_cases i <;> norm_num [signedMatrix] at h0
private theorem signed_nonproportional : ∀i j,i≠j→∀t:ℝ,signedMatrix i≠t • signedMatrix j := by
  intro i j hij t he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · norm_num [signedMatrix] at h0 h1
    linarith
  · norm_num [signedMatrix] at h0 h1
    linarith
  · exact (hij rfl).elim

private def signedLanguage : RealLanguage 2 2 2 where
  matrices := fun l=>if l=0 then signedMatrix else 0
  unaries := fun l i=>if l=i then -1 else 2
  weights := ![2,3]
  matrices_algebraic := by
    intro l i j
    fin_cases l <;> fin_cases i <;> fin_cases j <;>
      norm_num [signedMatrix] <;> first | exact isAlgebraic_one | exact isAlgebraic_zero |
        exact (isAlgebraic_nat (R:=ℚ) (A:=ℝ) 2).neg | exact isAlgebraic_nat 5
  unaries_algebraic := by
    intro l i
    split <;> first | exact isAlgebraic_one.neg | exact isAlgebraic_nat 2
  weights_algebraic := by
    intro i
    fin_cases i <;> first | exact isAlgebraic_nat 2 | exact isAlgebraic_nat 3

private theorem positive_weights : ∀i,0<signedLanguage.weights i := by
  intro i
  fin_cases i <;> norm_num [signedLanguage]

example (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
    (signedLanguage.domainProblem domains (withGlobalMatrix policy 0) typing) base) :
    PromisePolyTimeTuringReduction
      (signedLanguage.domainUnitWeightProblem domains (withGlobalMatrix policy 0) typing) base :=
  signedLanguage.lemma37_global_domain_removeWeights domains policy typing 0 1 (by simp [domains])
    signed_symm positive_weights signed_nonzero signed_nonproportional base available

example (r : ℚ) (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
    (signedLanguage.domainProblem domains (withGlobalMatrix policy 0) typing) base) :
    PromisePolyTimeTuringReduction
      (signedLanguage.domainRationalWeightProblem positive_weights r domains (withGlobalMatrix policy 0) typing 0) base :=
  signedLanguage.lemma37_global_domain_rational domains policy typing 0 1 (by simp [domains])
    signed_symm positive_weights signed_nonzero signed_nonproportional r base available

#print axioms RealLanguage.lemma37_global_domain_removeWeights
#print axioms RealLanguage.lemma37_global_domain_rational
#print axioms rawLoopComputer
