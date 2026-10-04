import PlanarHom.PottsCoefficientCorrectness
import PlanarHom.ParameterizedGraphReduction
import PlanarHom.PlanarRibbonExistence

/-! NEW reconstruction: same-q centered coefficient access is an actual
ordinary-planar raw-word polynomial-time oracle reduction. The input retains
noncanonical successfully decoded graph words and a canonical binary index. -/
noncomputable section
open Classical
namespace PlanarHom.PottsCoefficientReduction
open Complexity Complexity.MixedCode MachineComposition
open PottsCoefficientPrograms ProperColoringPottsReduction

abbrev RawInput := ℕ × BitEncoding.ValidWord MixedCode.encoding

def rawEncoding := ParameterizedMatrixEvaluation.inputEncoding BitEncoding.nat

def problem (q : ℕ) : PromiseProblem :=
  ⟨fun raw => ∃ p : RawInput,rawEncoding.encode p=raw ∧ p.2.value.PlanarValid 1 0,
    encodedFunction PottsCoefficientPrograms.inputEncoding fieldCode (coefficientValue q) []⟩

private def rawView (q : ℕ) (raw : Bits) (h : (problem q).valid raw) : RawInput := Classical.choose h

private theorem rawView_spec (q : ℕ) (raw : Bits) (h : (problem q).valid raw) :
    rawEncoding.encode (rawView q raw h)=raw ∧ (rawView q raw h).2.value.PlanarValid 1 0 :=
  Classical.choose_spec h

theorem value_raw_input (q : ℕ) (p : RawInput) :
    (problem q).value (rawEncoding.encode p)=
      fieldCode.encode (coefficientValue q (p.1,p.2.value)) := by
  simp only [problem,encodedFunction,PottsCoefficientPrograms.inputEncoding,rawEncoding,
    ParameterizedMatrixEvaluation.decode_raw_input]

/-- Actual input-normalizing preparation, every planar parallel query, actual
rational recovery, and the original positive-Potts answer-length bound. -/
def reduction (q : ℕ) (hq : 0<q) :
    PromisePolyTimeTuringReduction (problem q) (pottsProblem basis q) := by
  let pre := composeComputers
    (Classical.choice (ParameterizedMatrixEvaluation.fp_normalize BitEncoding.nat))
    (Classical.choice fp_prepare)
  let bound := evaluationProblem_output_bound basis
    (fun _ : Fin 1 => positivePottsMatrix q) (noUnaries q) (fun _ => 1)
  let p := Classical.choose bound
  have hp := Classical.choose_spec bound
  apply nonadaptiveReduction (p:=p) rawEncoding metaEncoding MixedCode.encoding fieldCode fieldCode
    (problem q) (pottsProblem basis q) (fun w => prepare (w.1,w.2.value))
    (sampleAnswer q) (recover q) pre (Classical.choice (fp_recover q))
    (rawView q) (fun raw h => (rawView_spec q raw h).1)
  · intro raw h query hquery
    have hg := (rawView_spec q raw h).2
    obtain ⟨k,_,_,rfl⟩ := GraphInterpolationQueries.mem_queries hquery
    exact ⟨_,MixedCode.encoding.decode_encode _,hg.parallelLabel 0 k⟩
  · intro query hquery
    obtain ⟨g,hd,hg⟩ := hquery
    rw [MixedCode.encoding.decode_encode] at hd
    cases Option.some.inj hd
    change evaluationValue basis (fun _ : Fin 1 => positivePottsMatrix q) (noUnaries q)
      (fun _ => 1) (MixedCode.encoding.encode query)=fieldCode.encode (sampleAnswer q query)
    rw [evaluationValue_encode _ _ _ _ _ hg.1,sampleAnswer,totalEvaluation_valid _ _ _ _ hg.1]
    rfl
  · intro raw h
    have hs := rawView_spec q raw h
    have hc := coefficient_recovery q hq (rawView q raw h).1 (rawView q raw h).2.value hs.2.1
    rw [hc]
    have hv := value_raw_input q (rawView q raw h)
    rw [hs.1] at hv
    exact hv.symm
  · exact hp
end PlanarHom.PottsCoefficientReduction
