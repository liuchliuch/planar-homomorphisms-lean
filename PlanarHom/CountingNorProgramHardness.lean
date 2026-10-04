import PlanarHom.CountingCookLevinSerializedCorrectness
import PlanarHom.PromisedSharpPHardness
import PlanarHom.NonadaptiveReductionCompiler
import PlanarHom.EncodingSizeBounds

/-! A genuine unconditional promised #P-hardness seed: counting fixed-length
inputs accepted by a materialized NOR straight-line program. The source is the
independent accepting-path machine class, compiled above with one-to-one counts. -/
noncomputable section
open Classical
namespace PlanarHom.CountingNorProgram
open Complexity CountingCookLevin SingleTapeNondeterministic PairProjectionMachines

/-- Number of free witness bits (unary), binary gate pairs, binary output wire.
Every gate deterministically appends its NOR value and its three fixed gadget
auxiliaries; only the original witness bits are counted. -/
abbrev Program := ℕ × (NorGates × ℕ)
def encoding : BitEncoding Program := BitEncoding.unaryNat.prod (gateEncoding.list.prod BitEncoding.nat)

def accepts (p : Program) (w : Fin p.1 → Bool) : Bool :=
  readBit (runNor p.2.1 (initialStore w)) p.2.2

def count (p : Program) : ℕ := Fintype.card {w : Fin p.1 → Bool // accepts p w=true}

/-- Canonical materialized encodings form the promise. -/
def problem : PromiseProblem :=
  ⟨fun raw => ∃ p,encoding.encode p=raw, encodedFunction encoding BitEncoding.nat count []⟩

def compileClocked (m : Machine) (p : ClockedInput) : Program :=
  (p.2,(uniformProgram m p,timeStart m (uniformBlockSize m) (finalContext p)+8))

theorem fp_compileClocked (m : Machine) : FP clockedEncoding encoding (compileClocked m) := by
  have hx := fp_fst BitEncoding.bits BitEncoding.unaryNat
  have hT := fp_snd BitEncoding.bits BitEncoding.unaryNat
  have hc : FP clockedEncoding refEncoding finalContext :=
    hx.pair (hT.pair ((hT.comp UnaryNatConversionMachine.fp_conversion).pair (fp_const _ _ 0)))
  have ho := ((hc.comp (fp_timeStart m (uniformBlockSize m))).pair
    (fp_const clockedEncoding BitEncoding.nat 8)).comp BinaryArithmetic.fp_addition
  exact hT.pair ((fp_uniformProgram m).pair ho)

def compile (M : PolynomialMachine) (x : Bits) : Program :=
  compileClocked M.machine (x,M.time.eval x.length)

theorem fp_compile (M : PolynomialMachine) : FP BitEncoding.bits encoding (compile M) :=
  (fp_polynomialClock M.time).comp (fp_compileClocked M.machine)

/-- Parsimonious compiler correctness, with the exact source witness length. -/
theorem count_compile (M : PolynomialMachine) (x : Bits) : count (compile M x)=M.count x :=
  (count_eq_serializedValue M x).symm

theorem count_le (p : Program) : count p≤2^p.1 := by
  have h := Fintype.card_subtype_le (fun w : Fin p.1 → Bool => accepts p w=true)
  simpa [count,Fintype.card_fun] using h

/-- Binary answers have linear size in the actual unary-witness program code. -/
theorem answer_length (raw : Bits) (h : problem.valid raw) :
    (problem.value raw).length≤(Polynomial.X+1 : Polynomial ℕ).eval raw.length := by
  obtain ⟨p,rfl⟩ := h
  change (encodedFunction encoding BitEncoding.nat count [] (encoding.encode p)).length≤_
  rw [encodedFunction_encode]
  have hc := EncodingSizeBounds.nat_encoding_length_le_of_le_pow (count_le p)
  have he : (encoding.encode p).length=2*p.1+
      ((gateEncoding.list.prod BitEncoding.nat).encode p.2).length+1 := by
    simp [encoding,BitEncoding.prod_length]
  rw [show Nat.size 2=2 by simpa using (Nat.size_pow (n := 1))] at hc
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  omega

/-- One real bit-costed promised query returns the source count. Oracle answer
length, materialized query construction, and answer copying are all charged. -/
def machineReduction (f : Bits → ℕ) (M : PolynomialMachine) (hf : ∀ x,f x=M.count x) :
    PromisePolyTimeTuringReduction (countingProblem f) problem := by
  let prepare : Bits → Bits × List Program := fun x => ([],[compile M x])
  have hp : FP BitEncoding.bits (BitEncoding.bits.prod encoding.list) prepare := by
    have hsingle := ((fp_compile M).pair (fp_const BitEncoding.bits encoding.list [])).comp
      (ListMutationMachines.fp_cons encoding)
    exact (fp_const BitEncoding.bits BitEncoding.bits []).pair hsingle
  let recover : Bits × List ℕ → ℕ := fun p => p.2.headD 0
  have hr : FP (BitEncoding.bits.prod BitEncoding.nat.list) BitEncoding.nat recover :=
    (fp_snd _ _).comp (ListDecompositionMachines.fp_headD BitEncoding.nat 0)
  apply nonadaptiveReduction BitEncoding.bits BitEncoding.bits encoding BitEncoding.nat BitEncoding.nat
    (countingProblem f) problem prepare count recover (Classical.choice hp) (Classical.choice hr)
    (fun raw _ => raw) (fun _ _ => rfl)
  · intro raw _ q _
    exact ⟨q,rfl⟩
  · intro q _
    exact encodedFunction_encode encoding BitEncoding.nat count [] q
  · intro raw _
    change BitEncoding.nat.encode (count (compile M raw))=BitEncoding.nat.encode (f raw)
    rw [count_compile,hf]
  · exact answer_length

/-- Unconditional promised #P hardness proved from the independent machine
class, not from a circuit-counting hardness assumption. -/
theorem promisedSharpPHard : PromisedSharpPHard problem := by
  intro f hf
  obtain ⟨M,hM⟩ := hf.singleTapeSharpP
  exact ⟨machineReduction f M hM⟩

end PlanarHom.CountingNorProgram
