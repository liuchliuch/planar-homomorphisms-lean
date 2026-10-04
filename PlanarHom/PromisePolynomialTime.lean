import PlanarHom.GraphNonadaptiveReduction
import PlanarHom.RestrictedListFoldMachines
import PlanarHom.MachineOutputTransport

/-! Promised polynomial time means an actual TM2 computer on the unchanged raw
input words. Proof-only input restrictions do not decide the promise and do not
supply an evaluator, advice, an oracle, or an answer-size bound. -/
noncomputable section
open Classical
namespace PlanarHom.Complexity

/-- Exact polynomial-time computation on every promised raw word. The input
codec is the identity on those words; the witness is a genuine TM2 program and
a polynomial time bound in the original raw length. -/
def PromiseProblem.InFP (P : PromiseProblem) : Prop :=
  FP (BitEncoding.bits.restrict P.valid) BitEncoding.bits (fun x => P.value x.val)

/-- Choose the genuine machine certified by promised membership. -/
def PromiseProblem.InFP.computer {P : PromiseProblem} (h : P.InFP) :
    Turing.TM2ComputableInPolyTime (BitEncoding.bits.restrict P.valid).toFinEncoding
      BitEncoding.bits.toFinEncoding (fun x => P.value x.val) := Classical.choice h

/-- Direct raw-word execution specification, charged against the literal input
length and requiring only membership in the mathematical promise. -/
def PromiseProblem.InFP.outputs {P : PromiseProblem} (h : P.InFP)
    (raw : Bits) (valid : P.valid raw) :
    Turing.TM2OutputsInTime h.computer.tm (raw.map h.computer.inputAlphabet.symm)
      (some ((P.value raw).map h.computer.outputAlphabet.symm))
      (h.computer.time.eval raw.length) :=
  h.computer.outputsFun ⟨raw,valid⟩

/-- Narrowing only the promise reuses the same actual program. -/
theorem PromiseProblem.InFP.mono {P Q : PromiseProblem} (h : P.InFP)
    (valid : ∀ x, Q.valid x → P.valid x)
    (value : ∀ x, Q.valid x → Q.value x = P.value x) : Q.InFP := by
  let view : {x // Q.valid x} → {x // P.valid x} := fun x => ⟨x.val,valid x.val x.property⟩
  have ht := h.transportInput (ea := BitEncoding.bits.restrict Q.valid) view (fun _ => rfl)
  exact ht.congr (fun x => (value x.val x.property).symm)

namespace MixedCode
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension b u : ℕ}

private def promisedRawView (H : MixedCode → Prop)
    (raw : {raw : Bits // ∃ g, encoding.decode raw=some g ∧ H g}) :
    BitEncoding.ValidWord encoding :=
  ⟨raw.val,by obtain ⟨g,hd,_⟩ := raw.property; exact ⟨g,hd⟩⟩

private theorem promisedRawView_property (H : MixedCode → Prop)
    (raw : {raw : Bits // ∃ g, encoding.decode raw=some g ∧ H g}) :
    H (promisedRawView H raw).value := by
  obtain ⟨g,hd,hg⟩ := raw.property
  have he : (promisedRawView H raw).value=g := BitEncoding.ValidWord.value_eq hd
  simpa only [he] using hg

/-- Canonical typed promised computation and arbitrary successful raw-input
promised computation are equivalent. The reverse implication actually runs the
existing graph normalizer before the typed computer, with raw input charging. -/
theorem restrictedEvaluation_inFP_iff (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (H : MixedCode → Prop) (valid : ∀ g, H g → g.Valid b u) :
    (restrictedEvaluationProblem basis M U w H).InFP ↔
      FP (encoding.restrict H) (numberFieldEncoding basis)
        (fun g : {g // H g} => g.val.evaluate (valid g.val g.property) M U w) := by
  constructor
  · intro h
    let view : {g // H g} → {raw : Bits // (restrictedEvaluationProblem basis M U w H).valid raw} :=
      fun g => ⟨encoding.encode g.val,⟨g.val,encoding.decode_encode g.val,g.property⟩⟩
    have ht := h.transportInput (ea := encoding.restrict H) view (fun _ => rfl)
    apply ht.transportOutput
    intro g
    exact evaluationValue_encode basis M U w g.val (valid g.val g.property)
  · intro h
    let input := BitEncoding.bits.restrict (restrictedEvaluationProblem basis M U w H).valid
    let value : {raw : Bits // (restrictedEvaluationProblem basis M U w H).valid raw} → {g // H g} :=
      fun raw => ⟨(promisedRawView H raw).value,promisedRawView_property H raw⟩
    have hv : FP input (BitEncoding.ValidWord.encoding encoding) (promisedRawView H) :=
      fp_code_view _ _ _ (fun _ => rfl)
    have hn : FP input (encoding.restrict H) value :=
      (hv.comp ⟨normalizer⟩).transportOutput (fun _ => rfl)
    apply (hn.comp h).transportOutput
    intro raw
    exact (evaluationValue_decode basis M U w raw.val (value raw).val
      (BitEncoding.ValidWord.decode_raw (promisedRawView H raw))
      (valid _ (value raw).property)).symm

/-- The ordinary planar promise, including noncanonical raw encodings, has the
same exact promised-TM2 class as the honestly encoded planar graph subtype. -/
theorem evaluation_inFP_iff (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K) :
    (evaluationProblem basis M U w).InFP ↔
      FP (encoding.restrict (PlanarValid b u)) (numberFieldEncoding basis)
        (fun g : {g : MixedCode // g.PlanarValid b u} => g.val.evaluate g.property.1 M U w) :=
  restrictedEvaluation_inFP_iff basis M U w (PlanarValid b u) (fun _ h => h.1)

end MixedCode
end PlanarHom.Complexity
