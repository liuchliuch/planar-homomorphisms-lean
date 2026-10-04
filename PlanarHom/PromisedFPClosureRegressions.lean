import PlanarHom.PromisedFPReductionClosure
import PlanarHom.OracleReductionLaws
import PlanarHom.PromiseReductionTransport

/-! NEW regressions for the reconstructed promised-FP closure. These retain the
baseline model and exercise raw words and arbitrary, possibly undecidable,
promises. No new hypothesis assumes the target's polynomial-time membership. -/
noncomputable section
namespace PlanarHom.Complexity.PromisedFPClosureRegressions
open Turing PlanarHom.MachineComposition

/-- Exact recovered public signature, with no extra representation, output-size,
algorithm, validity-decider, or target-FP assumption. -/
theorem recovered_signature : ∀ {P Q : PromiseProblem},
    PromisePolyTimeTuringReduction P Q → Q.InFP → P.InFP :=
  @PromisePolyTimeTuringReduction.inFP

/-- Both actual codecs are unchanged: the proof-carrying subtype adds no bits. -/
theorem raw_input_encoding (valid : Bits → Prop) (x : {x // valid x}) :
    (BitEncoding.bits.restrict valid).encode x = x.val := rfl

theorem raw_output_encoding (x : Bits) : BitEncoding.bits.encode x = x := rfl

/-- The ordinary program is definitionally the real substitution compiler. -/
theorem compiler_program {P Q : PromiseProblem}
    (r : PromisePolyTimeTuringReduction P Q)
    (s : TM2ComputableInPolyTime (BitEncoding.bits.restrict Q.valid).toFinEncoding
      BitEncoding.bits.toFinEncoding (fun x => Q.value x.val)) :
    (PromisedFPClosureReconstruction.computer r s).tm =
      OracleSubstitution.machine r.machine s.toTM2ComputableAux := rfl

/-- The time bound is definitionally the compiler's cumulative polynomial. -/
theorem compiler_time {P Q : PromiseProblem}
    (r : PromisePolyTimeTuringReduction P Q)
    (s : TM2ComputableInPolyTime (BitEncoding.bits.restrict Q.valid).toFinEncoding
      BitEncoding.bits.toFinEncoding (fun x => Q.value x.val)) :
    (PromisedFPClosureReconstruction.computer r s).time =
      OracleSubstitution.timePolynomial r.machine r.time s.time := rfl

/-- Full machine-output specification on a literal raw word. The input length
is exactly raw.length, rather than a canonical or represented replacement. -/
def raw_outputs {P Q : PromiseProblem} (r : PromisePolyTimeTuringReduction P Q)
    (s : TM2ComputableInPolyTime (BitEncoding.bits.restrict Q.valid).toFinEncoding
      BitEncoding.bits.toFinEncoding (fun x => Q.value x.val))
    (raw : Bits) (valid : P.valid raw) :
    TM2OutputsInTime (PromisedFPClosureReconstruction.computer r s).tm
      (raw.map (PromisedFPClosureReconstruction.computer r s).inputAlphabet.symm)
      (some ((P.value raw).map
        (PromisedFPClosureReconstruction.computer r s).outputAlphabet.symm))
      ((OracleSubstitution.timePolynomial r.machine r.time s.time).eval raw.length) :=
  (PromisedFPClosureReconstruction.computer r s).outputsFun ⟨raw, valid⟩

/-- The target output-size bound is derived from its resulting real machine. -/
theorem derived_output_length {P Q : PromiseProblem}
    (r : PromisePolyTimeTuringReduction P Q) (h : Q.InFP)
    (raw : Bits) (valid : P.valid raw) :
    (P.value raw).length ≤
      (outputLengthPolynomial (PromisedFPClosureReconstruction.computer r h.computer)).eval
        raw.length :=
  encoded_output_length_le (PromisedFPClosureReconstruction.computer r h.computer) ⟨raw,valid⟩

def identityProblem (valid : Bits → Prop) : PromiseProblem := ⟨valid, id⟩

theorem identity_solver (valid : Bits → Prop) : (identityProblem valid).InFP :=
  fp_code_view (BitEncoding.bits.restrict valid) BitEncoding.bits Subtype.val (fun _ => rfl)

/-- One real query on the same input/output stack, including the empty word. -/
def identityReduction (valid : Bits → Prop) :
    PromisePolyTimeTuringReduction (identityProblem valid) (identityProblem valid) :=
  PromisePolyTimeTuringReduction.refl_of_output_bound (identityProblem valid) Polynomial.X
    (by intro x _; simp [identityProblem])

theorem one_query (valid : Bits → Prop) : (identityProblem valid).InFP :=
  (identityReduction valid).inFP (identity_solver valid)

/-- Composition retains the all-extensions quantifier and promised query
validity before eliminating the external oracle. No promise decider is given. -/
theorem composed_queries (valid : Bits → Prop) : (identityProblem valid).InFP :=
  ((identityReduction valid).trans (identityReduction valid)).inFP (identity_solver valid)

/-- Source and target promises can differ; the computation still receives the
literal target word and queries only the (larger) source promise. -/
theorem distinct_promises (valid : Bits → Prop) : (identityProblem valid).InFP := by
  let r := (identityReduction (fun _ => True)).transport
    (identityProblem valid) (identityProblem (fun _ => True))
    (fun _ _ => trivial) (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl)
  exact r.inFP (identity_solver (fun _ => True))

/-- Empty target promise does not require evaluating its arbitrary value off
promise. The theorem supplies the same genuine compiled machine interface. -/
theorem empty_promise (value : Bits → Bits) : (PromiseProblem.mk (fun _ => False) value).InFP := by
  let r := (identityReduction (fun _ => True)).transport
    ⟨fun _ => False, value⟩ (identityProblem (fun _ => True))
    (fun _ _ => trivial) (fun _ h => h) (fun _ h => h.elim) (fun _ _ => rfl)
  exact r.inFP (identity_solver (fun _ => True))

/-- Boundary regression at the empty input word. -/
def empty_word_outputs :
    TM2OutputsInTime
      (PromisedFPClosureReconstruction.computer (identityReduction (fun _ => True))
        (identity_solver (fun _ => True)).computer).tm
      ([] : Bits)
      (some [])
      ((OracleSubstitution.timePolynomial (identityReduction (fun _ => True)).machine
        (identityReduction (fun _ => True)).time
        (identity_solver (fun _ => True)).computer.time).eval 0) := by
  simpa only [List.map_nil] using raw_outputs (identityReduction (fun _ => True))
    (identity_solver (fun _ => True)).computer [] trivial

/-- Recorded answers cannot be arbitrary advice, including on a nonempty raw
bit pattern; they are fixed by the real query-run constructor. -/
theorem concrete_transcript (oracle : Bits → Bits) :
    ∀ q a, (q,a) ∈ [([true,false,false,true], oracle [true,false,false,true])] → a = oracle q :=
  PromisedFPClosureReconstruction.transcript_answer
    (directQueryMachine_run oracle [true,false,false,true])

end PlanarHom.Complexity.PromisedFPClosureRegressions
