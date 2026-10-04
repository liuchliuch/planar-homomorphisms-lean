import PlanarHom.SurfaceFKTProgram
import PlanarHom.SurfaceFisherMatchingMachines

/-! NEW actual encoded preparation and representative-calibration machines. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace PlanarHom.SurfaceFKT
open Complexity SurfaceBooleanRows PairProjectionMachines ArithmeticCircuitPrimitives
open MultiGraph.Kasteleyn
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {d : ℕ}
variable (basis : Module.Basis (Fin d) ℚ K)

abbrev tableCode := (rowCode.prod (numberFieldEncoding basis)).list
abbrev partsCode := MixedCode.encoding.prod (MixedCode.encoding.prod
  (logCode.prod ((numberFieldEncoding basis).list.prod quotientDataCode)))

def preparedCode : BitEncoding (Prepared K) := (partsCode basis).retract
  (fun p => (p.cubic,p.graph,p.orientation,p.weights,p.quotient))
  (fun p => ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩) (by intro p;cases p;rfl)

theorem fp_parts : FP (preparedCode basis) (partsCode basis)
    (fun p => (p.cubic,p.graph,p.orientation,p.weights,p.quotient)) := fp_code_view _ _ _ (fun _ => rfl)
theorem fp_build : FP (partsCode basis) (preparedCode basis)
    (fun p => ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩) := fp_code_view _ _ _ (fun _ => rfl)
theorem fp_cubic : FP (preparedCode basis) MixedCode.encoding Prepared.cubic :=
  (fp_parts basis).comp (fp_fst _ _)
theorem fp_graph : FP (preparedCode basis) MixedCode.encoding Prepared.graph :=
  (fp_parts basis).comp ((fp_snd _ _).comp (fp_fst _ _))
theorem fp_orientation : FP (preparedCode basis) logCode Prepared.orientation :=
  (fp_parts basis).comp ((fp_snd _ _).comp ((fp_snd _ _).comp (fp_fst _ _)))
theorem fp_weights : FP (preparedCode basis) (numberFieldEncoding basis).list Prepared.weights :=
  (fp_parts basis).comp ((fp_snd _ _).comp ((fp_snd _ _).comp ((fp_snd _ _).comp (fp_fst _ _))))
theorem fp_quotient : FP (preparedCode basis) quotientDataCode Prepared.quotient :=
  (fp_parts basis).comp ((fp_snd _ _).comp ((fp_snd _ _).comp ((fp_snd _ _).comp (fp_snd _ _))))

theorem fp_prepare (ρ : K) : FP PlanarityRowFaceCode.inputCode (preparedCode basis)
    (fun p => prepare ρ p.1 p.2) := by
  have hd := (SurfaceFisherCode.fp_code.pair SurfaceFisherCode.fp_inheritedRows).comp SurfaceRawHomology.fp_data
  have h := (SurfaceFisherCode.fp_intermediate.pair
    (SurfaceFisherCode.fp_code.pair (SurfaceFisherCode.fp_orientationLog.pair
      ((SurfaceFisherCode.fp_weights basis ρ).pair hd)))).comp (fp_build basis)
  exact h.congr (fun _ => rfl)

theorem fp_characterValue : FP (rowCode.prod rowCode) (numberFieldEncoding basis)
    (fun p => characterValue (K:=K) p.1 p.2) := by
  let ep := BitEncoding.bool.prod BitEncoding.nat
  have hx := fp_fst rowCode ep
  have hp := fp_snd rowCode ep
  have hb := hp.comp (fp_fst BitEncoding.bool BitEncoding.nat)
  have hi := hp.comp (fp_snd BitEncoding.bool BitEncoding.nat)
  have hbit := (hb.pair ((hx.pair hi).comp fp_bitAt)).comp (fp_bool_gate (fun p => p.1 && p.2))
  have htest : FP (rowCode.prod ep) BitEncoding.bool
      (fun p => decide ((p.2.1 && bitAt p.1 p.2.2)=true)) := hbit.congr (fun _ => by simp)
  have hv := htest.ite (fp_const _ (numberFieldEncoding basis) (-1)) (fp_const _ _ 1)
  have hu := (fp_fst rowCode rowCode).comp (ListIndexMachines.fp_zipIdx BitEncoding.bool)
  have hx' := fp_snd rowCode rowCode
  exact ((hx'.pair hu).comp (ListContextMachines.fp_mapWithContext rowCode ep (numberFieldEncoding basis) _ hv)).comp
    (MaterializedFieldListMachines.fp_product basis)

theorem fp_characters (ambient : ℕ) : FP (preparedCode basis) rowCode.list (characters ambient) :=
  (((fp_quotient basis).comp (fp_snd basisCode basisCode)).comp
    (ListCodecMachines.fp_length SurfaceBooleanRows.pivotCode)).comp (fp_boundedWords (2*ambient))

theorem fp_supportWeights : FP ((preparedCode basis).prod rowCode) (numberFieldEncoding basis).list
    (fun p => supportWeights p.1 p.2) := by
  have hp := fp_fst (preparedCode basis) rowCode
  have hx := fp_snd (preparedCode basis) rowCode
  have hc := hp.comp (fp_cubic basis)
  have hq := hp.comp (fp_quotient basis)
  have hl := (hq.pair hx).comp fp_liftQuotient
  have hm := (hc.pair hl).comp SurfaceFisherMatching.fp_mask
  have hb : FP BitEncoding.bool (numberFieldEncoding basis) (fun b => if b then (1:K) else 0) :=
    ((fp_id BitEncoding.bool).congr (fun b => show b=decide (b=true) from by simp)).ite
      (fp_const _ _ 1) (fp_const _ _ 0)
  exact hm.comp (ListMapMachines.fp_map BitEncoding.bool (numberFieldEncoding basis) _ hb)

theorem fp_calibration : FP ((preparedCode basis).prod rowCode) (numberFieldEncoding basis)
    (fun p => calibration p.1 p.2) := by
  have hp := fp_fst (preparedCode basis) rowCode
  have hg := hp.comp (fp_graph basis)
  have hl := hp.comp (fp_orientation basis)
  have h := (hg.pair (hl.pair (fp_supportWeights basis))).comp (OccurrenceSkewCode.fp_evaluate basis)
  exact h.congr (fun _ => rfl)

theorem fp_calibrationTable (ambient : ℕ) : FP (preparedCode basis) (tableCode basis) (calibrationTable ambient) :=
  ((fp_id (preparedCode basis)).pair (fp_characters basis ambient)).comp
    (ListContextMachines.fp_mapWithContext (preparedCode basis) rowCode
      (rowCode.prod (numberFieldEncoding basis)) _
      ((fp_snd (preparedCode basis) rowCode).pair (fp_calibration basis)))

end PlanarHom.SurfaceFKT
