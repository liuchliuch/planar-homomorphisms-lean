import PlanarHom.ColoringEmitterLocalMachines
import PlanarHom.UnaryPolynomialMachines

/-! NEW actual finite-control machines for emitting one macro and its dictionary
allocation. No finite graph enumeration oracle is used. -/
namespace PlanarHom.ColoringEmitter
open Complexity PositiveBlockProgram PairProjectionMachines ArithmeticCircuitPrimitives

theorem fp_kindCases {A B : Type} (ea : BitEncoding A) (eb : BitEncoding B)
    (f : A→Kind→B) (hf : ∀k,FP ea eb (fun x=>f x k)) :
    FP (ea.prod kindEncoding) eb (fun p=>f p.1 p.2) := by
  have hx:=fp_fst ea kindEncoding
  have hk:=(fp_snd ea kindEncoding).comp fp_kindCode
  have hhi:=hk.comp (fp_fst BitEncoding.bool BitEncoding.bool)
  have hlo:=hk.comp (fp_snd BitEncoding.bool BitEncoding.bool)
  have hfalse:=(hlo.pair ((hx.comp (hf .cross)).pair (hx.comp (hf .wire)))).comp (ConditionalMachines.fp_select eb)
  have htrue:=(hlo.pair ((hx.comp (hf .test)).pair (hx.comp (hf .fan)))).comp (ConditionalMachines.fp_select eb)
  exact ((hhi.pair (htrue.pair hfalse)).comp (ConditionalMachines.fp_select eb)).congr
    (fun p=>by rcases p with ⟨x,k⟩; cases k <;> rfl)

theorem fp_fixedListMap {A B C : Type} (ea : BitEncoding A) (ec : BitEncoding C)
    (xs : List B) (f : A→B→C) (hf : ∀b∈xs,FP ea ec (fun x=>f x b)) :
    FP ea ec.list (fun x=>xs.map (f x)) := by
  induction xs with
  | nil => exact fp_const ea ec.list []
  | cons b bs ih =>
    exact ((hf b (by simp)).pair (ih (fun b hb=>hf b (by simp [hb])))).comp
      (ListMutationMachines.fp_cons ec)

theorem fp_freshDictionary_fixed (k : Kind) : FP BitEncoding.nat BitEncoding.nat.list
    (fun base=>freshDictionary base k) := by
  apply fp_fixedListMap BitEncoding.nat BitEncoding.nat (List.range k.template.fresh)
  intro i _
  by_cases hi:i<Macro.outputCount k
  · exact (((fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.nat (3*i))).comp
      BinaryArithmetic.fp_addition).congr (fun base=>by simp [hi])
  · exact (fp_const BitEncoding.nat BitEncoding.nat 0).congr (fun _=>by simp [hi])

theorem fp_freshDictionary : FP (BitEncoding.nat.prod kindEncoding) BitEncoding.nat.list
    (fun p=>freshDictionary p.1 p.2) :=
  fp_kindCases BitEncoding.nat BitEncoding.nat.list freshDictionary fp_freshDictionary_fixed

theorem fp_emitEdges : FP (stateEncoding.prod instructionEncoding) edgeEncoding.list
    (fun p=>emitEdges p.1 p.2) := by
  let pairCode:=BitEncoding.nat.prod BitEncoding.nat
  have hs:=fp_fst stateEncoding instructionEncoding
  have hop:=fp_snd stateEncoding instructionEncoding
  have hbase:=(hs.comp fp_vertices).comp UnaryNatConversionMachine.fp_conversion
  have hctx:=hop.pair ((hs.comp fp_dictionary).pair hbase)
  have htab:=(hop.comp (fp_fst kindEncoding referenceEncoding)).comp (fp_kindFunction pairCode.list Macro.edges)
  have hc:=fp_fst contextEncoding pairCode
  have hp:=fp_snd contextEncoding pairCode
  have hleft:=(hc.pair (hp.comp (fp_fst BitEncoding.nat BitEncoding.nat))).comp fp_localVertex
  have hright:=(hc.pair (hp.comp (fp_snd BitEncoding.nat BitEncoding.nat))).comp fp_localVertex
  have hbody:=hleft.pair (hright.pair (fp_const (contextEncoding.prod pairCode) BitEncoding.nat 0))
  exact (hctx.pair htab).comp (ListContextMachines.fp_mapWithContext contextEncoding pairCode edgeEncoding _ hbody)

theorem fp_step : FP (stateEncoding.prod instructionEncoding) stateEncoding
    (fun p=>step p.1 p.2) := by
  have hs:=fp_fst stateEncoding instructionEncoding
  have hop:=fp_snd stateEncoding instructionEncoding
  have hk:=hop.comp (fp_fst kindEncoding referenceEncoding)
  have hsource:=((hs.comp fp_sourceBase).pair
    (hk.comp (fp_kindFunction BitEncoding.unaryNat (fun k=>k.template.fresh)))).comp UnaryPolynomialMachines.fp_add
  have hbase:=hs.comp fp_vertices
  have hnew:=((hbase.comp UnaryNatConversionMachine.fp_conversion).pair hk).comp fp_freshDictionary
  have hdict:=((hs.comp fp_dictionary).pair hnew).comp (ListMutationMachines.fp_append BitEncoding.nat)
  have hcount:=(hbase.pair (hk.comp (fp_kindFunction BitEncoding.unaryNat Macro.addedVertices))).comp
    UnaryPolynomialMachines.fp_add
  have hedges:=((hs.comp fp_edges).pair fp_emitEdges).comp (ListMutationMachines.fp_append edgeEncoding)
  exact (hsource.pair (hdict.pair (hcount.pair hedges))).comp fp_build

theorem fp_initial : FP BitEncoding.unaryNat stateEncoding initial := by
  have hn:=fp_id BitEncoding.unaryNat
  have hd:=(fp_range.comp (ListMapMachines.fp_map BitEncoding.nat BitEncoding.nat (fun i=>3*i)
    (((fp_const BitEncoding.nat BitEncoding.nat 3).pair (fp_id BitEncoding.nat)).comp BinaryArithmetic.fp_multiplication)))
  have hv:=((fp_const BitEncoding.unaryNat BitEncoding.unaryNat 3).pair hn).comp UnaryPolynomialMachines.fp_mul
  have he:=fp_const BitEncoding.unaryNat edgeEncoding.list []
  exact (hn.pair (hd.pair (hv.pair he))).comp fp_build

theorem fp_graphOf : FP stateEncoding MixedCode.encoding graphOf := by
  have h:=(fp_vertices.pair (fp_edges.pair
    (fp_const stateEncoding (BitEncoding.nat.prod BitEncoding.nat).list [])))
  exact h.transportOutput (fun _=>rfl)

end PlanarHom.ColoringEmitter
