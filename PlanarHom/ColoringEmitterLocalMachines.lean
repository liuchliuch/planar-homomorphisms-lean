import PlanarHom.ColoringEmitterCodecs

/-! NEW actual local address translation machines. Every selected address is
read from the literal dictionary or allocated after the actual graph header. -/
namespace PlanarHom.ColoringEmitter
open Complexity PositiveBlockProgram PairProjectionMachines ArithmeticCircuitPrimitives

theorem fp_address : FP (kindEncoding.prod BitEncoding.nat) addressEncoding
    (fun p=>Macro.address p.1 p.2) :=
  (((fp_fst kindEncoding BitEncoding.nat).comp (fp_kindFunction addressEncoding.list Macro.addresses)).pair
    (fp_snd kindEncoding BitEncoding.nat)).comp (fp_getD addressEncoding (2,0,0))

theorem fp_inputRef : FP (instructionEncoding.prod BitEncoding.nat) BitEncoding.nat
    (fun p=>inputRef p.1 p.2) := by
  have ho:=fp_fst instructionEncoding BitEncoding.nat
  have hi:=fp_snd instructionEncoding BitEncoding.nat
  have hr:=ho.comp (fp_snd kindEncoding referenceEncoding)
  have h0:=hr.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have h12:=hr.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have h1:=h12.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have h2:=h12.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hnil:=fp_const (instructionEncoding.prod BitEncoding.nat) BitEncoding.nat.list []
  have hxs:=(h0.pair ((h1.pair ((h2.pair hnil).comp (ListMutationMachines.fp_cons BitEncoding.nat))).comp
    (ListMutationMachines.fp_cons BitEncoding.nat))).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  exact (hxs.pair hi).comp (fp_getD BitEncoding.nat 0)

theorem fp_localVertex : FP (contextEncoding.prod BitEncoding.nat) BitEncoding.nat
    (fun p=>localVertex p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let ec:=contextEncoding.prod BitEncoding.nat
  have hc:=fp_fst contextEncoding BitEncoding.nat
  have hv:=fp_snd contextEncoding BitEncoding.nat
  have hop:=hc.comp (fp_fst instructionEncoding (BitEncoding.nat.list.prod BitEncoding.nat))
  have hdb:=hc.comp (fp_snd instructionEncoding (BitEncoding.nat.list.prod BitEncoding.nat))
  have hd:=hdb.comp (fp_fst BitEncoding.nat.list BitEncoding.nat)
  have hb:=hdb.comp (fp_snd BitEncoding.nat.list BitEncoding.nat)
  have hk:=hop.comp (fp_fst kindEncoding referenceEncoding)
  have ha:=(hk.pair hv).comp fp_address
  have ht:=ha.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hjc:=ha.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hj:=hjc.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hch:=hjc.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have href:=(hop.pair hj).comp fp_inputRef
  have hold:=((hd.pair href).comp (fp_getD BitEncoding.nat 0)).pair hch
  have hin:=hold.comp BinaryArithmetic.fp_addition
  have hthree:=fp_const ec BitEncoding.nat 3
  have hnew:=((hb.pair ((hthree.pair hj).comp BinaryArithmetic.fp_multiplication)).comp BinaryArithmetic.fp_addition).pair hch
  have hout:=hnew.comp BinaryArithmetic.fp_addition
  have hcount:=hk.comp (fp_kindFunction BitEncoding.nat Macro.outputCount)
  have hpriv:=(((hb.pair ((hthree.pair hcount).comp BinaryArithmetic.fp_multiplication)).comp
    BinaryArithmetic.fp_addition).pair hj).comp BinaryArithmetic.fp_addition
  have ht0:=(ht.pair (fp_const ec BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  have ht1:=(ht.pair (fp_const ec BitEncoding.nat 1)).comp NatListSumMachines.fp_equal
  exact ht0.ite hin (ht1.ite hout hpriv)

end PlanarHom.ColoringEmitter
