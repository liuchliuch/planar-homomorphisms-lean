import PlanarHom.FisherWeightMachines
import PlanarHom.OccurrenceOrientationLogMachines
import PlanarHom.MaterializedFieldListMachines

/-! NEW runtime of literal reference-matching calibration: canonical endpoint
signs times the parity of actual crossing occurrence pairs. -/
namespace PlanarHom.FisherCubicCode
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives FisherCodeMachines MultiGraph.Kasteleyn

 theorem fp_referencePorts : FP graphVertexCode slotCode
    (fun p=>(portNumber p.1 (p.2,false),portNumber p.1 (p.2,true))) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have he:=fp_snd MixedCode.encoding BitEncoding.nat
  exact ((hg.pair (he.pair (fp_const graphVertexCode BitEncoding.bool false))).comp fp_portNumber).pair
    ((hg.pair (he.pair (fp_const graphVertexCode BitEncoding.bool true))).comp fp_portNumber)

 theorem fp_referenceLower : FP graphVertexCode BitEncoding.nat (fun p=>referenceLower p.1 p.2) :=
  fp_referencePorts.comp PlanarityLRRawConstraints.fp_min

 theorem fp_referenceUpper : FP graphVertexCode BitEncoding.nat (fun p=>referenceUpper p.1 p.2) := by
  have hs:=fp_referencePorts.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have ht:=fp_referencePorts.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  exact ((fp_referencePorts.comp PlanarityLRRawConstraints.fp_le).ite ht hs).congr
    (fun _=>by simp only [Function.comp_apply,referenceUpper]; split_ifs with h <;> simp [max_def,h])

 theorem fp_referenceCross : FP (MixedCode.encoding.prod slotCode) BitEncoding.bool
    (fun p=>referenceCross p.1 p.2.1 p.2.2) := by
  have hg:=fp_fst MixedCode.encoding slotCode
  have hep:=fp_snd MixedCode.encoding slotCode
  have he:=hep.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hf:=hep.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hle:=(hg.pair he).comp fp_referenceLower
  have hlf:=(hg.pair hf).comp fp_referenceLower
  have hue:=(hg.pair he).comp fp_referenceUpper
  have huf:=(hg.pair hf).comp fp_referenceUpper
  have h₁:=(hle.pair hlf).comp BinaryArithmetic.fp_comparison
  have h₂:=(hlf.pair hue).comp BinaryArithmetic.fp_comparison
  have h₃:=(hue.pair huf).comp BinaryArithmetic.fp_comparison
  exact ((h₁.pair ((h₂.pair h₃).comp (fp_bool_gate (fun p=>p.1 && p.2)))).comp (fp_bool_gate (fun p=>p.1 && p.2))).congr
    (fun p=>by simp [referenceCross])

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

 theorem fp_referenceEdgeSign : FP ((MixedCode.encoding.prod logCode).prod BitEncoding.nat)
    (numberFieldEncoding basis) (fun p=>referenceEdgeSign p.1.1 p.1.2 p.2) := by
  let ek:=numberFieldEncoding basis
  let ei:=(MixedCode.encoding.prod logCode).prod BitEncoding.nat
  have hc:=fp_fst (MixedCode.encoding.prod logCode) BitEncoding.nat
  have he:=fp_snd (MixedCode.encoding.prod logCode) BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding logCode)
  have hl:=hc.comp (fp_snd MixedCode.encoding logCode)
  have hb : FP ei BitEncoding.bool (fun p=>decide (logOrientation p.1.2 p.2=true)) :=
    ((hl.pair he).comp fp_logOrientation).congr (fun _=>by simp)
  have hs:=hb.ite (fp_const ei ek 1) (fp_const ei ek (-1))
  have horder:=((hg.pair he).comp fp_referencePorts).comp BinaryArithmetic.fp_comparison
  exact horder.ite hs (hs.comp (FixedFieldArithmetic.fp_negation basis))

 theorem fp_referenceSign : FP (MixedCode.encoding.prod logCode)
    (numberFieldEncoding basis) (fun p=>referenceSign p.1 p.2) := by
  let ek:=numberFieldEncoding basis
  let ec:=MixedCode.encoding.prod logCode
  have hg:=fp_fst MixedCode.encoding logCode
  have hr:=hg.comp PlanarityLRRawConstraints.fp_edgeRange
  have hsigns:=((fp_id ec).pair hr).comp
    (ListContextMachines.fp_mapWithContext ec BitEncoding.nat ek _ (fp_referenceEdgeSign basis))
  have hleft:=hsigns.comp (MaterializedFieldListMachines.fp_product basis)
  have hc:=fp_fst graphVertexCode BitEncoding.nat
  have hf:=fp_snd graphVertexCode BitEncoding.nat
  have hg₁:=hc.comp (fp_fst MixedCode.encoding BitEncoding.nat)
  have he:=hc.comp (fp_snd MixedCode.encoding BitEncoding.nat)
  have hcross:=(hg₁.pair (he.pair hf)).comp fp_referenceCross
  have hcross' : FP (graphVertexCode.prod BitEncoding.nat) BitEncoding.bool
      (fun p=>decide (referenceCross p.1.1 p.1.2 p.2=true)) := hcross.congr (fun _=>by simp)
  have hitem:=hcross'.ite
    (fp_const (graphVertexCode.prod BitEncoding.nat) ek (-1)) (fp_const _ ek 1)
  have hr₁:=(fp_fst MixedCode.encoding BitEncoding.nat).comp PlanarityLRRawConstraints.fp_edgeRange
  have hrow:=((fp_id graphVertexCode).pair hr₁).comp
    (ListContextMachines.fp_mapWithContext graphVertexCode BitEncoding.nat ek _ hitem)
  have hmatrix:=((fp_id MixedCode.encoding).pair PlanarityLRRawConstraints.fp_edgeRange).comp
    (fp_flatMap MixedCode.encoding BitEncoding.nat ek
      (fun g e=>(List.range g.edges.length).map (fun f=>if referenceCross g e f then (-1:K) else 1)) hrow)
  have hright:=(hg.comp hmatrix).comp (MaterializedFieldListMachines.fp_product basis)
  exact (hleft.pair hright).comp (FixedFieldArithmetic.fp_multiplication basis)

end PlanarHom.FisherCubicCode
