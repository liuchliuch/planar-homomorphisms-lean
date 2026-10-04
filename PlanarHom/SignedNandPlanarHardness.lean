import PlanarHom.SignedNandIncidence
import PlanarHom.SignedNandNumericSemantics
import PlanarHom.ProperColoringNaturalReduction

/-! Unconditional ordinary-planar signed-NAND hardness. Queries are honest
mixed incidence codes with unit background, Boolean NAND edges and one unary
[1,-1] at each fresh clause center. Target promises admit all valid raw codes. -/
noncomputable section
open Classical
namespace PlanarHom.SignedNandPlanarHardness
open Complexity Complexity.MixedCode ParsimoniousNorOneInThree PairProjectionMachines
open ProperColoringPottsReduction

abbrev matrices := SignedNandNumeric.matrices
abbrev unaries := SignedNandNumeric.unaries

def problem : PromiseProblem := evaluationProblem rationalBasis matrices unaries (fun _ => 1)

def compile (f : NumericFormula) : MixedCode := SignedNandNumeric.compile (PositiveRoutingCompiler.compile f)

theorem fp_compile : FP formulaEncoding MixedCode.encoding compile :=
  PositiveRoutingCompiler.fp_compile.comp SignedNandNumeric.fp_compile

theorem compile_planar (f : NumericFormula) (hf : NumericValid f) : (compile f).PlanarValid 1 1 :=
  SignedNandNumeric.compile_planar f hf

theorem compile_value (f : NumericFormula) (hf : NumericValid f) :
    totalEvaluation matrices unaries (fun _ => 1) (compile f)=(CountingPositiveOneInThree.count f : ℚ) := by
  rw [totalEvaluation_valid _ _ _ _ (compile_planar f hf).1]
  change (SignedNandNumeric.compile (PositiveRoutingCompiler.compile f)).evaluate
    (SignedNandNumeric.compile_valid _ (PositiveRoutingCompiler.compile_valid f hf))
    SignedNandNumeric.matrices SignedNandNumeric.unaries (fun _ => 1)=_
  rw [SignedNandNumeric.evaluate_eq_count _ (PositiveRoutingCompiler.compile_valid f hf),
    PositiveRoutingCompiler.count_preserved f hf]

/-- Preparation includes full positive-formula routing, signed graph emission,
normalization and NAND edge coalescing. Recovery reads the exact rational
numerator, with all answer sizes bounded by the ordinary evaluation API. -/
def reduction : PromisePolyTimeTuringReduction CountingPositiveOneInThree.problem problem := by
  let answerEncoding := numberFieldEncoding rationalBasis
  let prepare : NumericFormula → Bits × List MixedCode := fun f => ([],[compile f])
  have hp : FP formulaEncoding (BitEncoding.bits.prod MixedCode.encoding.list) prepare := by
    have hs := (fp_compile.pair (fp_const formulaEncoding MixedCode.encoding.list [])).comp
      (ListMutationMachines.fp_cons MixedCode.encoding)
    exact (fp_const formulaEncoding BitEncoding.bits []).pair hs
  let recover : Bits × List ℚ → ℕ := fun p => p.2.prod.num.natAbs
  have hr : FP (BitEncoding.bits.prod answerEncoding.list) BitEncoding.nat recover :=
    ((fp_snd _ _).comp (MaterializedFieldListMachines.fp_product rationalBasis)).comp fp_extractNatural
  let view : ∀raw,CountingPositiveOneInThree.problem.valid raw → NumericFormula := fun _ h => Classical.choose h
  have same : ∀raw h,formulaEncoding.encode (view raw h)=raw := fun _ h => (Classical.choose_spec h).2
  have hv : ∀raw h,NumericValid (view raw h) := fun _ h => (Classical.choose_spec h).1
  let bound := evaluationProblem_output_bound rationalBasis matrices unaries (fun _ => 1)
  let p := Classical.choose bound
  have hbound := Classical.choose_spec bound
  apply nonadaptiveReduction (p:=p) formulaEncoding BitEncoding.bits MixedCode.encoding answerEncoding BitEncoding.nat
    CountingPositiveOneInThree.problem problem prepare (totalEvaluation matrices unaries (fun _ => 1)) recover
    (Classical.choice hp) (Classical.choice hr) view same
  · intro raw h q hq
    have he : q=compile (view raw h) := by simpa [prepare] using hq
    subst q
    exact ⟨_,MixedCode.encoding.decode_encode _,compile_planar _ (hv raw h)⟩
  · intro q hq
    obtain ⟨g,hd,hg⟩ := hq
    rw [MixedCode.encoding.decode_encode] at hd
    cases Option.some.inj hd
    exact (evaluationValue_encode rationalBasis matrices unaries (fun _ => 1) q hg.1).trans
      (congrArg answerEncoding.encode (totalEvaluation_valid matrices unaries (fun _ => 1) q hg.1).symm)
  · intro raw h
    change BitEncoding.nat.encode (([totalEvaluation matrices unaries (fun _ => 1) (compile (view raw h))]).prod.num.natAbs)=_
    simp only [List.prod_cons,List.prod_nil,mul_one]
    rw [compile_value _ (hv raw h),extractNatural_natCast]
    change _=encodedFunction formulaEncoding BitEncoding.nat CountingPositiveOneInThree.count [] raw
    conv_rhs => rw [←same raw h,encodedFunction_encode]
  · exact hbound

/-- Genuine #P-hardness from the independent accepting-path source. No
counting-SAT, planarity, gadget-existence, or source-hardness premise remains. -/
theorem promisedSharpPHard : PromisedSharpPHard problem :=
  CountingPositiveOneInThree.promisedSharpPHard.trans reduction

end PlanarHom.SignedNandPlanarHardness
