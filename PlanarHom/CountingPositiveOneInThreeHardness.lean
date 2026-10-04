import PlanarHom.NorExactOneSemantics
import PlanarHom.NorExactOneMachines

/-! An unconditional promised #P-hardness theorem for fully materialized positive
exactly-one-in-three formulas, by one actual parsimonious NOR-program query. -/
noncomputable section
open Classical
namespace PlanarHom.NorExactOne
open Complexity CountingCookLevin ParsimoniousNorOneInThree

theorem checkedRef_lt (n z i : ℕ) (hz : z<n) : checkedRef n z i<n := by
  by_cases hi : i<n <;> simp [checkedRef,hi,hz]

theorem compile_valid (p : CountingNorProgram.Program) : NumericValid (compile p) := by
  let m := p.1+4+4*p.2.1.length
  have hv : (compile p).1=m+3 := compile_variables p
  intro c hc
  rw [compile_clauses] at hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · simp only [pin,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl <;> rw [hv] <;> dsimp [m] <;> omega
    · have h := network_refs p.2.1 (p.1+4) (p.1+1) c hc
      rw [hv]
      dsimp [m]
      omega
  · have ht := checkedRef_lt m (p.1+1) p.2.2 (by dsimp [m]; omega)
    change c∈pin m (checkedRef m (p.1+1) p.2.2) at hc
    simp only [pin,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl <;> rw [hv] <;> dsimp <;> omega

end PlanarHom.NorExactOne

namespace PlanarHom.CountingPositiveOneInThree
open Complexity ParsimoniousNorOneInThree PairProjectionMachines

abbrev Formula := NumericFormula
abbrev encoding : BitEncoding Formula := formulaEncoding

def count (f : Formula) : ℕ := Fintype.card (NorExactOne.Solutions f)

/-- Canonical codes with all clause coordinates below the declared unary count.
Clause positions may repeat; their Boolean values retain literal multiplicity. -/
def problem : PromiseProblem :=
  ⟨fun raw => ∃ f,NumericValid f ∧ encoding.encode f=raw,
    encodedFunction encoding BitEncoding.nat count []⟩

@[simp] theorem count_compile (p : CountingNorProgram.Program) :
    count (NorExactOne.compile p)=CountingNorProgram.count p :=
  NorExactOne.count_preserved p

theorem count_le (f : Formula) : count f≤2^f.1 := by
  have h := Fintype.card_subtype_le
    (fun σ : Fin f.1 → Bool => Satisfies f.2 (CountingCookLevin.readBit (List.ofFn σ)))
  simpa [count,Fintype.card_fun] using h

/-- The oracle response is linearly bounded in the actual encoded formula. -/
theorem answer_length (raw : Bits) (h : problem.valid raw) :
    (problem.value raw).length≤(Polynomial.X+1 : Polynomial ℕ).eval raw.length := by
  obtain ⟨f,hf,rfl⟩ := h
  change (encodedFunction encoding BitEncoding.nat count [] (encoding.encode f)).length≤_
  rw [encodedFunction_encode]
  have hc := EncodingSizeBounds.nat_encoding_length_le_of_le_pow (count_le f)
  have he : (encoding.encode f).length=2*f.1+(clauseEncoding.list.encode f.2).length+1 := by
    simp [encoding,formulaEncoding,BitEncoding.prod_length]
  rw [show Nat.size 2=2 by simpa using (Nat.size_pow (n := 1))] at hc
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  omega

/-- A single promise-valid query with exact integer recovery. Preparation,
query bits, answer bits, and copying/recovery are charged by actual machines. -/
def reduction : PromisePolyTimeTuringReduction CountingNorProgram.problem problem := by
  let prepare : CountingNorProgram.Program → Bits × List Formula :=
    fun p => ([],[NorExactOne.compile p])
  have hp : FP CountingNorProgram.encoding (BitEncoding.bits.prod encoding.list) prepare := by
    have hs := ((NorExactOne.fp_compile).pair
      (fp_const CountingNorProgram.encoding encoding.list [])).comp (ListMutationMachines.fp_cons encoding)
    exact (fp_const CountingNorProgram.encoding BitEncoding.bits []).pair hs
  let recover : Bits × List ℕ → ℕ := fun p => p.2.headD 0
  have hr : FP (BitEncoding.bits.prod BitEncoding.nat.list) BitEncoding.nat recover :=
    (fp_snd _ _).comp (ListDecompositionMachines.fp_headD BitEncoding.nat 0)
  let view : ∀ raw,CountingNorProgram.problem.valid raw → CountingNorProgram.Program :=
    fun _ h => Classical.choose h
  have same : ∀ raw h,CountingNorProgram.encoding.encode (view raw h)=raw :=
    fun _ h => Classical.choose_spec h
  apply nonadaptiveReduction CountingNorProgram.encoding BitEncoding.bits encoding BitEncoding.nat BitEncoding.nat
    CountingNorProgram.problem problem prepare count recover (Classical.choice hp) (Classical.choice hr) view same
  · intro raw h q hq
    have he : q=NorExactOne.compile (view raw h) := by simpa [prepare] using hq
    subst q
    exact ⟨_,NorExactOne.compile_valid _,rfl⟩
  · intro q _
    exact encodedFunction_encode encoding BitEncoding.nat count [] q
  · intro raw h
    change BitEncoding.nat.encode (count (NorExactOne.compile (view raw h)))=_
    rw [count_compile]
    change _=encodedFunction CountingNorProgram.encoding BitEncoding.nat CountingNorProgram.count [] raw
    conv_rhs => rw [←same raw h,encodedFunction_encode]
  · exact answer_length

/-- From the independent accepting-path #P class, without a counting-SAT or
circuit-hardness assumption and without a cardinality factor. -/
theorem promisedSharpPHard : PromisedSharpPHard problem :=
  CountingNorProgram.promisedSharpPHard.trans reduction

end PlanarHom.CountingPositiveOneInThree
