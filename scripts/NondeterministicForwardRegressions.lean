import PlanarHom.NondeterministicCertificateBridge

namespace PlanarHom.NondeterministicForwardRegressions
open Complexity NondeterministicTM2 NondeterministicComputationTree

/-- Two labelled choices deliberately share exactly the same successor. -/
def duplicateBranch : Machine where
  core := {
    tm := {
      K := Unit
      Γ := fun _ => Bool
      k₀ := ()
      k₁ := ()
      Λ := Bool
      main := false
      σ := Unit
      initialState := ()
      Γk₀Fin := inferInstance
      m := fun _ => .push () (fun _ => true) .halt }
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool }
  finiteAlphabet := fun _ => inferInstance
  branch := fun b => if b then none else some (true,true)

theorem duplicateBranch_bounded (x : Bits) :
    Bounded duplicateBranch.view (duplicateBranch.initial x) 2 := by
  refine Bounded.binary (view := duplicateBranch.view) (n:=1) rfl ?_ ?_
  all_goals
    refine Bounded.ordinary (view := duplicateBranch.view) (n:=0) rfl ?_
    by_cases hx : x=[]
    · subst x
      exact Bounded.accept rfl
    · apply Bounded.reject
      simp [Machine.view,Machine.output,Machine.jump,Machine.initial,duplicateBranch,
        Turing.initList,Turing.TM2.stepAux,hx]

noncomputable def duplicatePolynomialMachine : PolynomialNondeterministicMachine where
  machine := duplicateBranch
  time := Polynomial.C 2
  halts x := by simpa using duplicateBranch_bounded x

example : duplicatePolynomialMachine.count [] = 2 := by
  simp only [PolynomialNondeterministicMachine.count,duplicatePolynomialMachine,Polynomial.eval_C]
  rfl
example : CertificateSharpP duplicatePolynomialMachine.count :=
  duplicatePolynomialMachine.certificateSharpP_count

example : acceptingCount duplicateBranch.view 2 (duplicateBranch.initial []) = 2 := rfl
example : acceptingCount duplicateBranch.view 1 (duplicateBranch.initial []) = 0 := rfl
example : acceptingCount duplicateBranch.view 2 (duplicateBranch.initial [false]) = 0 := rfl

-- One choice bit, then one forced-zero ordinary halt-transition bit.
example : NondeterministicReplayCompiler.verifier duplicateBranch ([],[false,false]) = true := rfl
example : NondeterministicReplayCompiler.verifier duplicateBranch ([],[true,false]) = true := rfl
example : NondeterministicReplayCompiler.verifier duplicateBranch ([],[false,true]) = false := rfl
example : NondeterministicReplayCompiler.verifier duplicateBranch ([],[true,true]) = false := rfl
-- A missing halt-transition bit rejects; all unused positions are uniquely zero.
example : NondeterministicReplayCompiler.verifier duplicateBranch ([],[false]) = false := rfl
example : NondeterministicReplayCompiler.verifier duplicateBranch ([],[false,false,false]) = true := rfl
example : NondeterministicReplayCompiler.verifier duplicateBranch ([],[false,false,true]) = false := rfl

example : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool
    (NondeterministicReplayCompiler.verifier duplicateBranch) :=
  NondeterministicReplayCompiler.fp_verifier duplicateBranch

example (f : Bits → ℕ) (h : SharpP f) : CertificateSharpP f := h.certificateSharpP
example (g : Bits → Bits) (h : CertificateSharpPHard g) : SharpPHard g := h.sharpPHard

#check NondeterministicReplayCompiler.computer
#check PolynomialNondeterministicMachine.count_eq_card_complete_paths
#check PolynomialNondeterministicMachine.count_eq_certificateCount
#check acceptingPathEquivCertificates
#print axioms NondeterministicReplayCompiler.computer
#print axioms SharpP.certificateSharpP
#print axioms CertificateSharpPHard.sharpPHard

end PlanarHom.NondeterministicForwardRegressions
