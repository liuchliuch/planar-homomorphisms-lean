import PlanarHom.CertificateGeneratorCorrectness
import PlanarHom.NondeterministicSharpP

/-!
# Compiling polynomial certificate verifiers to nondeterministic machines

An actual deterministic preparation machine computes the certificate length in
unary. A finite-alphabet binary-choice machine then generates exactly that many
bits and runs the original verifier. Each certificate contributes exactly one
computation, and the complete machine has an explicit polynomial clock.
-/

namespace PlanarHom.CertificateNondeterministicCompiler

noncomputable section

open Turing Complexity NondeterministicComputationTree Polynomial

/-- Preparation computes the raw input together with its unary certificate length. -/
theorem fp_preparation (p : Polynomial ℕ) :
    FP BitEncoding.bits (BitEncoding.bits.prod BitEncoding.unaryNat)
      (fun x : Bits => (x, p.eval x.length)) := by
  have hlength : FP BitEncoding.bits BitEncoding.unaryNat (fun x : Bits => x.length) :=
    ⟨InputLengthMachine.computer BitEncoding.bits⟩
  exact (fp_id BitEncoding.bits).pair (hlength.comp (UnaryPolynomialMachines.fp_eval p))

/-- The proved ordinary machine implementing preparation. -/
def preparationSource (p : Polynomial ℕ) :
    TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding
      (BitEncoding.bits.prod BitEncoding.unaryNat).toFinEncoding
      (fun x : Bits => (x, p.eval x.length)) :=
  Classical.choice (fp_preparation p)

/-- Preparation with every inaccessible alphabet symbol removed. -/
def preparation (p : Polynomial ℕ) :
    TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding
      (BitEncoding.bits.prod BitEncoding.unaryNat).toFinEncoding
      (fun x : Bits => (x, p.eval x.length)) :=
  FiniteReachableAlphabetMachines.restrictComputer (preparationSource p)

/-- The given verifier with finite alphabets on every stack. -/
def verification (V : Bits × Bits → Bool)
    (hV : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool V) :
    TM2ComputableInPolyTime (BitEncoding.bits.prod BitEncoding.bits).toFinEncoding
      BitEncoding.bool.toFinEncoding V :=
  FiniteReachableAlphabetMachines.restrictComputer (Classical.choice hV)

/-- The actual preparation, branching-generator, and verifier program. -/
def machine (p : Polynomial ℕ) (V : Bits × Bits → Bool)
    (hV : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool V) :
    NondeterministicTM2.Machine :=
  CertificateGeneratorMachine.machine (preparation p).toTM2ComputableAux
    (verification V hV).toTM2ComputableAux
    (FiniteReachableAlphabetMachines.alphabetFintype (preparationSource p))
    (FiniteReachableAlphabetMachines.alphabetFintype (Classical.choice hV))

/-- Preparation time, linear framing/generation time, and verifier time on its
physically serialized input. -/
def time (p : Polynomial ℕ) (V : Bits × Bits → Bool)
    (hV : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool V) : Polynomial ℕ :=
  (preparation p).time + C 3 * X + C 4 + C 3 * p +
    (verification V hV).time.comp (C 2 * X + C 1 + p)

/-- Every branch halts within the stated clock, with exactly the certificate count. -/
theorem run_correct (p : Polynomial ℕ) (V : Bits × Bits → Bool)
    (hV : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool V) (x : Bits) :
    Bounded (machine p V hV).view ((machine p V hV).initial x)
      ((time p V hV).eval x.length) ∧
    acceptingCount (machine p V hV).view ((time p V hV).eval x.length)
      ((machine p V hV).initial x) = certificateCount p V x := by
  let a := preparation p
  let b := verification V hV
  have hp : TM2OutputsInTime a.tm (x.map a.inputAlphabet.symm)
      (some ((BitEncoding.frame x ++ Computability.unaryEncodeNat (p.eval x.length)).map
        a.outputAlphabet.symm)) (a.time.eval x.length) := by
    exact a.outputsFun x
  have hv (w : Bits) (hw : w.length = p.eval x.length) :
      TM2OutputsInTime b.tm ((BitEncoding.frame x ++ w).map b.inputAlphabet.symm)
        (some ([V (x, w)].map b.outputAlphabet.symm))
        (b.time.eval (2 * x.length + 1 + p.eval x.length)) := by
    simpa only [BitEncoding.toFinEncoding, BitEncoding.prod, BitEncoding.bits, BitEncoding.bool,
      id_eq, List.length_append, BitEncoding.frame_length, hw] using b.outputsFun (x, w)
  have h := CertificateGeneratorMachine.run_correct a.toTM2ComputableAux b.toTM2ComputableAux
    (FiniteReachableAlphabetMachines.alphabetFintype (preparationSource p))
    (FiniteReachableAlphabetMachines.alphabetFintype (Classical.choice hV))
    x (p.eval x.length) (a.time.eval x.length)
    (b.time.eval (2 * x.length + 1 + p.eval x.length)) (fun w => V (x, w)) hp hv
  simpa only [machine, time, certificateCount, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp, a, b] using h

/-- A polynomial-time nondeterministic machine compiled from any ordinary
polynomial-time verifier and any natural-coefficient certificate-length polynomial. -/
def compile (p : Polynomial ℕ) (V : Bits × Bits → Bool)
    (hV : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool V) :
    PolynomialNondeterministicMachine where
  machine := machine p V hV
  time := time p V hV
  halts x := (run_correct p V hV x).1

/-- Parsimonious compilation: every accepted certificate contributes one path. -/
theorem count_eq_certificateCount (p : Polynomial ℕ) (V : Bits × Bits → Bool)
    (hV : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool V) (x : Bits) :
    (compile p V hV).count x = certificateCount p V x :=
  (run_correct p V hV x).2

end

end PlanarHom.CertificateNondeterministicCompiler

namespace PlanarHom.Complexity

/-- Every polynomial-certificate count is an independent nondeterministic
finite-alphabet TM2 accepting-path count. -/
theorem CertificateSharpP.sharpP {f : Bits → ℕ} (h : CertificateSharpP f) : SharpP f := by
  obtain ⟨p, V, hV, hf⟩ := h
  refine ⟨CertificateNondeterministicCompiler.compile p V hV, fun x => ?_⟩
  exact (hf x).trans (CertificateNondeterministicCompiler.count_eq_certificateCount p V hV x).symm

end PlanarHom.Complexity
