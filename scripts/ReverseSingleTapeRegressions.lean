import PlanarHom.SingleTapeSharpPBridge

namespace PlanarHom.ReverseSingleTapeRegressions
open Complexity NondeterministicComputationTree NondeterministicTM2
open TM2SingleTapeCounting TM2SingleTapeCompiler NondeterministicTM2SpaceBounds

/-- Both labelled choices deliberately have the same continuation. Nonempty
input is rejected, making a trailing false distinguishable from blank. -/
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
    · subst x; exact Bounded.accept rfl
    · apply Bounded.reject
      simp [Machine.view,Machine.output,Machine.jump,Machine.initial,duplicateBranch,
        Turing.initList,Turing.TM2.stepAux,hx]

noncomputable def sourceMachine : PolynomialNondeterministicMachine where
  machine := duplicateBranch
  time := Polynomial.C 2
  halts x := by simpa using duplicateBranch_bounded x

-- Empty input preserves both coincident binary alternatives.
example : (polynomialCompile sourceMachine).count [] = 2 := by
  rw [polynomialCompile_count]
  simp only [PolynomialNondeterministicMachine.count,sourceMachine,Polynomial.eval_C]
  rfl

-- A literal final zero cannot disappear into the tape's blank quotient.
example : (polynomialCompile sourceMachine).count [false] = 0 := by
  rw [polynomialCompile_count]
  simp only [PolynomialNondeterministicMachine.count,sourceMachine,Polynomial.eval_C]
  rfl
example : (polynomialCompile sourceMachine).count [true,false] = 0 := by
  rw [polynomialCompile_count]
  simp only [PolynomialNondeterministicMachine.count,sourceMachine,Polynomial.eval_C]
  rfl

-- A two-symbol output is rejected by the concrete two-cell checker.
example : (polynomialCompile sourceMachine).count [true] = 0 := by
  rw [polynomialCompile_count]
  simp only [PolynomialNondeterministicMachine.count,sourceMachine,Polynomial.eval_C]
  rfl

-- The compiled rejecting computations have the same all-branch clock guarantee.
example : Bounded (polynomialCompile sourceMachine).machine.view
    ((polynomialCompile sourceMachine).machine.initial [false])
    ((polynomialCompile sourceMachine).time.eval 1) :=
  (polynomialCompile sourceMachine).halts [false]

-- Enlarging a sufficient target clock never multiplies accepted computations.
example (x : Bits) (padding : ℕ) :
    acceptingCount (polynomialCompile sourceMachine).machine.view
      ((polynomialCompile sourceMachine).time.eval x.length+padding)
      ((polynomialCompile sourceMachine).machine.initial x) = sourceMachine.count x := by
  rw [(polynomialCompile sourceMachine).halts x |>.acceptingCount_add padding]
  exact polynomialCompile_count _ _

-- A source terminal leaf uses zero source transitions but two actual target
-- checker steps; acceptance remains a single complete computation.
example (m : Source) (c : m.Cfg) (size : ℕ)
    (hsize : ∀k,(c.stk k).length≤size)
    (L : Turing.ListBlank (∀k,Option (m.core.tm.Γ k)))
    (hL : Represents m c L) (hl : c.l=none) (ho : m.output c=[true]) :
    acceptingCount (compile m).view
      (TM2SingleTapeClock.blockCost m (TM2SingleTapePrimitiveRuns.primitiveBound m) size)
      (represented m c L) = 1 := by
  have hh : m.view c=.accept := by simp [Machine.view,hl,ho]
  have hs : Space m size 0 c := ⟨size,hsize,by simp⟩
  simpa [acceptingCount,hh] using
    (represented_correct m c (Bounded.accept hh (n:=0)) hs L hL).2

-- Exactly one zero-length certificate survives the entire actual compiler chain.
theorem true_verifier_fp : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool
    (fun _ : Bits × Bits => true) := fp_const _ _ true
example (x : Bits) :
    (polynomialCompile (CertificateNondeterministicCompiler.compile 0
      (fun _ => true) true_verifier_fp)).count x = 1 := by
  rw [polynomialCompile_count,CertificateNondeterministicCompiler.count_eq_certificateCount]
  simp [certificateCount]

example (f : Bits → ℕ) : SharpP f ↔ SingleTapeNondeterministic.SingleTapeSharpP f :=
  sharpP_iff_singleTapeSharpP f
example (f : Bits → ℕ) : CertificateSharpP f ↔ SingleTapeNondeterministic.SingleTapeSharpP f :=
  certificateSharpP_iff_singleTapeSharpP f
example (g : Bits → Bits) : SharpPHard g ↔ SingleTapeNondeterministic.SingleTapeSharpPHard g :=
  sharpPHard_iff_singleTapeSharpPHard g
example (g : Bits → Bits) : CertificateSharpPHard g ↔ SingleTapeNondeterministic.SingleTapeSharpPHard g :=
  certificateSharpPHard_iff_singleTapeSharpPHard g

#check TM2SingleTapeCounting.input_correct
#check TM2SingleTapeCounting.polynomialCompile_count
#check SharpP.singleTapeSharpP
#check CertificateSharpP.singleTapeSharpP
#check certificateSharpP_iff_singleTapeSharpP
end PlanarHom.ReverseSingleTapeRegressions
