import PlanarHom.FKTIsingMachines
import PlanarHom.FKTIsingCorrectness
import PlanarHom.FixedFieldPolynomialMachines

/-! NEW genuinely uniform Ising runtime: the occurrence graph and interaction
parameter are both encoded inputs. Dynamic products are charged to the joint
input length by the materialized fixed-field list machines. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace PlanarHom.FKTIsingUniform
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives MachineComposition
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)
abbrev inputCode := MixedCode.encoding.prod (numberFieldEncoding basis)

theorem fp_highTemperature : FP (numberFieldEncoding basis) (numberFieldEncoding basis)
    (fun ρ:K => (1-ρ)/(1+ρ)) := by
  have hpair := (fp_const (numberFieldEncoding basis) (numberFieldEncoding basis) 1).pair
    (fp_id (numberFieldEncoding basis))
  exact ((hpair.comp (FixedFieldArithmetic.fp_subtraction basis)).pair
    (hpair.comp (FixedFieldArithmetic.fp_addition basis))).comp (FixedFieldArithmetic.fp_division basis)

theorem fp_isingWeights : FP (inputCode basis) (numberFieldEncoding basis).list
    (fun p => FisherCodePipeline.isingWeights p.2 p.1) := by
  let ek := numberFieldEncoding basis
  let ee := FisherCodeMachines.edgeCode
  have hr := (fp_snd MixedCode.encoding ek).comp (fp_highTemperature basis)
  have he := (fp_fst MixedCode.encoding ek).comp MixedCode.fp_edges
  have hm := (hr.pair he).comp
    (ListContextMachines.fp_mapWithContext ek ee ek Prod.fst (fp_fst ek ee))
  exact hm.congr (fun p => by simp [FisherCodePipeline.isingWeights])

theorem fp_isingData : FP (inputCode basis) (MixedCode.encoding.prod (numberFieldEncoding basis).list)
    (fun p => FisherCodePipeline.isingData p.2 p.1) := by
  have hg := fp_fst MixedCode.encoding (numberFieldEncoding basis)
  have hr := hg.comp FisherContourOrder.fp_computedRows
  have hew := ((hg.pair hr).pair (fp_isingWeights basis)).comp
    (FisherExpansionCode.fp_weights (numberFieldEncoding basis))
  have hH := hg.comp FisherCodePipeline.fp_intermediate
  have hw := (hH.pair hew).comp (FisherCubicCode.fp_weights basis)
  exact (hg.comp FisherCodePipeline.fp_code).pair hw

theorem fp_normalization : FP (inputCode basis) (numberFieldEncoding basis)
    (fun p => FisherCodePipeline.normalization p.2 p.1) := by
  let ek := numberFieldEncoding basis
  let ee := FisherCodeMachines.edgeCode
  have hg := fp_fst MixedCode.encoding ek
  have hρ := fp_snd MixedCode.encoding ek
  have hone := fp_const (inputCode basis) ek 1
  have htwo := fp_const (inputCode basis) ek 2
  have ha := (((hone.pair hρ).comp (FixedFieldArithmetic.fp_addition basis)).pair htwo).comp
    (FixedFieldArithmetic.fp_division basis)
  have he := hg.comp MixedCode.fp_edges
  have hlist := (ha.pair he).comp
    (ListContextMachines.fp_mapWithContext ek ee ek Prod.fst (fp_fst ek ee))
  have hnum := hlist.comp (MaterializedFieldListMachines.fp_product basis)
  have hden := (hg.comp MixedCode.fp_vertices).comp (FixedPowerMachines.fp_power basis (2:K))
  have h := (hnum.pair hden).comp (FixedFieldArithmetic.fp_division basis)
  exact h.congr (fun p => by simp [FisherCodePipeline.normalization,List.map_const',List.prod_replicate])

theorem fp_pfaffianInput : FP (inputCode basis) (OccurrenceSkewCode.dataEncoding basis)
    (fun p => FKTIsingMachines.pfaffianInput p.2 p.1) := by
  have hg := fp_fst MixedCode.encoding (numberFieldEncoding basis)
  have hc := hg.comp FKTIsingMachines.fp_code
  have ho := hg.comp FKTIsingMachines.fp_orientation
  have hw := (fp_isingData basis).comp (fp_snd MixedCode.encoding (numberFieldEncoding basis).list)
  exact hc.pair (ho.pair hw)

theorem fp_referenceSign : FP MixedCode.encoding (numberFieldEncoding basis)
    (fun g => FisherCubicCode.referenceSign (K:=K)
      (FisherCodePipeline.intermediate g) (FKTIsingMachines.orientation g)) := by
  exact (FisherExpansionCode.fp_computed.pair FKTIsingMachines.fp_orientation).comp
    (FisherCubicCode.fp_referenceSign basis)

theorem fp_matchingValue : FP (inputCode basis) (numberFieldEncoding basis)
    (fun p => FKTIsingMachines.matchingValue p.2 p.1) := by
  have hsign : FP (inputCode basis) (numberFieldEncoding basis)
      (fun p => FisherCubicCode.referenceSign (K:=K)
        (FisherCodePipeline.intermediate p.1) (FKTIsingMachines.orientation p.1)) :=
    (fp_fst MixedCode.encoding (numberFieldEncoding basis)).comp (fp_referenceSign basis)
  have hpf : FP (inputCode basis) (numberFieldEncoding basis)
      (fun p => PfaffianList.evaluateGrid
        (OccurrenceSkewCode.grid (FKTIsingMachines.pfaffianInput p.2 p.1))) :=
    (fp_pfaffianInput basis).comp (OccurrenceSkewCode.fp_evaluate basis)
  exact (hsign.pair hpf).comp (FixedFieldArithmetic.fp_multiplication basis)

/-- One actual machine and one polynomial bound work for every graph and every
encoded parameter, including invalid graphs and the singular parameter -1. -/
theorem fp_value : FP (inputCode basis) (numberFieldEncoding basis)
    (fun p => FKTIsingMachines.value p.2 p.1) := by
  have h := ((fp_normalization basis).pair (fp_matchingValue basis)).comp
    (FixedFieldArithmetic.fp_multiplication basis)
  exact h.congr (fun _ => rfl)

theorem joint_output_bound : ∃p:Polynomial ℕ,∀g:MixedCode,∀ρ:K,
    ((numberFieldEncoding basis).encode (FKTIsingMachines.value ρ g)).length≤
      p.eval (((inputCode basis).encode (g,ρ)).length) := by
  obtain ⟨computer⟩ := fp_value basis
  exact ⟨outputLengthPolynomial computer,fun g ρ => encoded_output_length_le computer (g,ρ)⟩

end PlanarHom.FKTIsingUniform
