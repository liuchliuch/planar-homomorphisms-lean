import PlanarHom.RadialPottsEndpointMachines
import PlanarHom.ListMutationMachines

/-! The complete numeric radial assembly is compiled to an actual TM2 running
in polynomial time. Every loop dimension is unary and all edges are emitted. -/
namespace PlanarHom.RadialPotts.Numeric
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

 def tileContextEncoding := inputEncoding.prod BitEncoding.unaryNat
 def ringContextEncoding := tileContextEncoding.prod BitEncoding.unaryNat

 theorem fp_longEntries : FP ringContextEncoding edgeEncoding.list (fun x : (Input×ℕ)×ℕ =>
    (List.range 4).flatMap (fun s => (List.range (x.2+1)).map (longEntry x.1.1 x.1.2 x.2 s))) := by
  let es := ringContextEncoding.prod BitEncoding.unaryNat
  let eall := es.prod BitEncoding.unaryNat
  have hctx := fp_fst es BitEncoding.unaryNat
  have ha := fp_snd es BitEncoding.unaryNat
  have hs := hctx.comp (fp_snd ringContextEncoding BitEncoding.unaryNat)
  have hbase := hctx.comp (fp_fst ringContextEncoding BitEncoding.unaryNat)
  have hr := hbase.comp (fp_snd tileContextEncoding BitEncoding.unaryNat)
  have ht := hbase.comp (fp_fst tileContextEncoding BitEncoding.unaryNat)
  have he := ht.comp (fp_snd inputEncoding BitEncoding.unaryNat)
  have hp := ht.comp (fp_fst inputEncoding BitEncoding.unaryNat)
  have hentry := fp_longEntry hp (he.comp UnaryNatConversionMachine.fp_conversion)
    (hr.comp UnaryNatConversionMachine.fp_conversion) (hs.comp UnaryNatConversionMachine.fp_conversion)
    (ha.comp UnaryNatConversionMachine.fp_conversion)
  have hrow := (fp_fst ringContextEncoding BitEncoding.unaryNat).comp
    (fp_snd tileContextEncoding BitEncoding.unaryNat)
  have hn := (hrow.pair (fp_const es BitEncoding.unaryNat 1)).comp UnaryPolynomialMachines.fp_add
  have hm := fp_rangeMap hn _ hentry
  exact fp_rangeFlatMap (fp_const ringContextEncoding BitEncoding.unaryNat 4) _ hm

 theorem fp_shortEntries : FP ringContextEncoding edgeEncoding.list (fun x : (Input×ℕ)×ℕ =>
    (List.range (4*x.2+2)).flatMap (fun j =>
      [shortEntry x.1.1.2.1 x.1.2 x.2 j false,shortEntry x.1.1.2.1 x.1.2 x.2 j true])) := by
  let ej := ringContextEncoding.prod BitEncoding.unaryNat
  have hbase := fp_fst ringContextEncoding BitEncoding.unaryNat
  have hj := fp_snd ringContextEncoding BitEncoding.unaryNat
  have hr := hbase.comp (fp_snd tileContextEncoding BitEncoding.unaryNat)
  have ht := hbase.comp (fp_fst tileContextEncoding BitEncoding.unaryNat)
  have he := ht.comp (fp_snd inputEncoding BitEncoding.unaryNat)
  have hp := ht.comp (fp_fst inputEncoding BitEncoding.unaryNat)
  have hred := fp_shortEntry (fp_inputK hp) (he.comp UnaryNatConversionMachine.fp_conversion)
    (hr.comp UnaryNatConversionMachine.fp_conversion) (hj.comp UnaryNatConversionMachine.fp_conversion) false
  have hblue := fp_shortEntry (fp_inputK hp) (he.comp UnaryNatConversionMachine.fp_conversion)
    (hr.comp UnaryNatConversionMachine.fp_conversion) (hj.comp UnaryNatConversionMachine.fp_conversion) true
  have hlist := (hred.pair ((hblue.pair (fp_const ej edgeEncoding.list [])).comp
    (ListMutationMachines.fp_cons edgeEncoding))).comp (ListMutationMachines.fp_cons edgeEncoding)
  have hrow := fp_snd tileContextEncoding BitEncoding.unaryNat
  have hfour := ((fp_const ringContextEncoding BitEncoding.unaryNat 4).pair hrow).comp UnaryPolynomialMachines.fp_mul
  have hn := (hfour.pair (fp_const ringContextEncoding BitEncoding.unaryNat 2)).comp UnaryPolynomialMachines.fp_add
  exact fp_rangeFlatMap hn _ hlist

 theorem fp_ringEntries : FP ringContextEncoding edgeEncoding.list
    (fun x : (Input×ℕ)×ℕ => ringEntries x.1.1 x.1.2 x.2) :=
  (fp_longEntries.pair fp_shortEntries).comp (ListMutationMachines.fp_append edgeEncoding)

 theorem fp_tileEntries : FP tileContextEncoding edgeEncoding.list (fun x : Input×ℕ =>
    (List.range x.1.2.1).flatMap (ringEntries x.1 x.2)) := by
  have hp := fp_fst inputEncoding BitEncoding.unaryNat
  have hk := (hp.comp (fp_snd _ _)).comp (fp_fst _ _)
  exact fp_rangeFlatMap hk _ fp_ringEntries

 theorem fp_edgeEntries : FP inputEncoding edgeEncoding.list edgeEntries :=
  fp_rangeFlatMap (fp_fst _ _) _ fp_tileEntries

 theorem fp_vertexCount : FP inputEncoding BitEncoding.unaryNat (fun p => Assembly.vertexCount p.1 p.2.1) := by
  have hm := fp_fst BitEncoding.unaryNat (BitEncoding.unaryNat.prod BitEncoding.nat.list)
  have hk := (fp_snd BitEncoding.unaryNat (BitEncoding.unaryNat.prod BitEncoding.nat.list)).comp
    (fp_fst BitEncoding.unaryNat BitEncoding.nat.list)
  have hkk := (hk.pair hk).comp UnaryPolynomialMachines.fp_mul
  have hw := ((fp_const inputEncoding BitEncoding.unaryNat 4).pair hkk).comp UnaryPolynomialMachines.fp_mul
  have hwhite := (hm.pair hw).comp UnaryPolynomialMachines.fp_mul
  have h2m := ((fp_const inputEncoding BitEncoding.unaryNat 2).pair hm).comp UnaryPolynomialMachines.fp_mul
  have hports := (h2m.pair hk).comp UnaryPolynomialMachines.fp_mul
  exact ((hwhite.pair hports).comp UnaryPolynomialMachines.fp_add).congr
    (fun _ => by simp only [Assembly.vertexCount,pow_two,Function.comp_apply])

/-- Unconditional polynomial-time numeric assembly, including arbitrary inverse
lists. Domain validity and planarity are proved separately on actual rotations. -/
theorem fp_output : FP inputEncoding MixedCode.encoding output := by
  have hb : FP (BitEncoding.unaryNat.prod (edgeEncoding.list.prod (BitEncoding.nat.prod BitEncoding.nat).list))
      MixedCode.encoding (fun p => ⟨p.1,p.2.1,p.2.2⟩) := fp_code_view _ _ _ (fun _ => rfl)
  exact (fp_vertexCount.pair (fp_edgeEntries.pair
    (fp_const inputEncoding (BitEncoding.nat.prod BitEncoding.nat).list []))).comp hb
end PlanarHom.RadialPotts.Numeric
