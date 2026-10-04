import PlanarHom.SurfaceFKTPreparationMachines

/-! NEW encoded runtime for the complete bounded-character Fourier evaluator.
The actual calibration table is computed before the weighted character fold. -/
set_option maxHeartbeats 2000000
namespace PlanarHom.SurfaceFKT
open Complexity SurfaceBooleanRows PairProjectionMachines ArithmeticCircuitPrimitives
open MultiGraph.Kasteleyn
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {d : ℕ}
variable (basis : Module.Basis (Fin d) ℚ K)

theorem fp_walsh : FP ((tableCode basis).prod rowCode) (numberFieldEncoding basis)
    (fun p => walsh p.1 p.2) := by
  let ek := numberFieldEncoding basis
  let ep := rowCode.prod ek
  have hu := fp_fst rowCode ep
  have hp := fp_snd rowCode ep
  have hx := hp.comp (fp_fst rowCode ek)
  have hv := hp.comp (fp_snd rowCode ek)
  have hbody := (((hu.pair hx).comp (fp_characterValue basis)).pair hv).comp (FixedFieldArithmetic.fp_multiplication basis)
  have ht := fp_fst (tableCode basis) rowCode
  have hu' := fp_snd (tableCode basis) rowCode
  exact ((hu'.pair ht).comp (ListContextMachines.fp_mapWithContext rowCode ep ek _ hbody)).comp
    (MaterializedFieldListMachines.fp_sum basis)

theorem fp_referenceCoordinates : FP (preparedCode basis) rowCode referenceCoordinates := by
  have hm := ((fp_cubic basis).pair (fp_const (preparedCode basis) rowCode [])).comp SurfaceFisherMatching.fp_mask
  exact ((fp_quotient basis).pair hm).comp fp_encodeQuotient

theorem fp_twistedWeights : FP ((preparedCode basis).prod rowCode) (numberFieldEncoding basis).list
    (fun p => twistedWeights p.1 p.2) := by
  let ek := numberFieldEncoding basis
  let ec := (preparedCode basis).prod rowCode
  let ee := OccurrenceSkewCode.edgeEncoding.prod BitEncoding.nat
  have hc := fp_fst ec ee
  have hp := hc.comp (fp_fst (preparedCode basis) rowCode)
  have hu := hc.comp (fp_snd (preparedCode basis) rowCode)
  have hi := (fp_snd ec ee).comp (fp_snd OccurrenceSkewCode.edgeEncoding BitEncoding.nat)
  have hq := hp.comp (fp_quotient basis)
  have hshape := (hp.comp (fp_graph basis)).comp SurfaceRawHomology.fp_shape
  have hunit := (hshape.pair hi).comp fp_unit
  have hcoords := (hq.pair hunit).comp fp_encodeQuotient
  have hchar := (hu.pair hcoords).comp (fp_characterValue basis)
  have hw := ((hp.comp (fp_weights basis)).pair hi).comp (FisherCodeMachines.fp_getD ek 0)
  have hbody := (hw.pair hchar).comp (FixedFieldArithmetic.fp_multiplication basis)
  have hgraph := (fp_fst (preparedCode basis) rowCode).comp (fp_graph basis)
  have hxs := (hgraph.comp MixedCode.fp_edges).comp (ListIndexMachines.fp_zipIdx OccurrenceSkewCode.edgeEncoding)
  exact ((fp_id ec).pair hxs).comp (ListContextMachines.fp_mapWithContext ec ee ek _ hbody)

theorem fp_twistedEvaluation : FP ((preparedCode basis).prod rowCode) (numberFieldEncoding basis)
    (fun p => twistedEvaluation p.1 p.2) := by
  have hp := fp_fst (preparedCode basis) rowCode
  have hu := fp_snd (preparedCode basis) rowCode
  have href := hp.comp (fp_referenceCoordinates basis)
  have hchar := (hu.pair href).comp (fp_characterValue basis)
  have hdata := (hp.comp (fp_graph basis)).pair ((hp.comp (fp_orientation basis)).pair (fp_twistedWeights basis))
  have hpf := hdata.comp (OccurrenceSkewCode.fp_evaluate basis)
  have h := (hchar.pair hpf).comp (FixedFieldArithmetic.fp_multiplication basis)
  exact h.congr (fun _ => rfl)

theorem fp_reciprocalDimension : FP (preparedCode basis) (numberFieldEncoding basis) reciprocalDimension :=
  (((fp_quotient basis).comp (fp_snd basisCode basisCode)).comp
    (ListMapMachines.fp_map SurfaceBooleanRows.pivotCode (numberFieldEncoding basis) (fun _ => (2:K)⁻¹)
      (fp_const _ _ (2:K)⁻¹))).comp (MaterializedFieldListMachines.fp_product basis)

theorem fp_matchingValue (ambient : ℕ) : FP (preparedCode basis) (numberFieldEncoding basis) (matchingValue ambient) := by
  let ek := numberFieldEncoding basis
  let ep := rowCode.prod ek
  let ec := (preparedCode basis).prod (tableCode basis)
  have hc := fp_fst ec ep
  have hp := hc.comp (fp_fst (preparedCode basis) (tableCode basis))
  have ht := hc.comp (fp_snd (preparedCode basis) (tableCode basis))
  have hu := (fp_snd ec ep).comp (fp_fst rowCode ek)
  have hw := (ht.pair hu).comp (fp_walsh basis)
  have hpf := (hp.pair hu).comp (fp_twistedEvaluation basis)
  have hbody := (hw.pair hpf).comp (FixedFieldArithmetic.fp_multiplication basis)
  have hm := ((fp_id ec).pair (fp_snd (preparedCode basis) (tableCode basis))).comp
    (ListContextMachines.fp_mapWithContext ec ep ek _ hbody)
  have hs := hm.comp (MaterializedFieldListMachines.fp_sum basis)
  have htable := (fp_id (preparedCode basis)).pair (fp_calibrationTable basis ambient)
  have hsum := htable.comp hs
  have h := ((fp_reciprocalDimension basis).pair hsum).comp (FixedFieldArithmetic.fp_multiplication basis)
  exact h.congr (fun _ => rfl)

theorem fp_value (ambient : ℕ) (ρ : K) : FP PlanarityRowFaceCode.inputCode (numberFieldEncoding basis)
    (fun p => value ambient ρ p.1 p.2) := by
  have hn := (fp_fst MixedCode.encoding PlanarityRowFaceCode.rowsCode).comp (FisherCodePipeline.fp_normalization basis ρ)
  have hm := (fp_prepare basis ρ).comp (fp_matchingValue basis ambient)
  have h := (hn.pair hm).comp (FixedFieldArithmetic.fp_multiplication basis)
  exact h.congr (fun _ => rfl)

end PlanarHom.SurfaceFKT
