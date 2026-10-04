import PlanarHom.ExponentVectors
import PlanarHom.UnaryRangeMachines
import PlanarHom.UnaryNatConversionMachine
import PlanarHom.NatListSumMachines
import PlanarHom.ContextFilterMachines
import PlanarHom.ListFlattenMachines

/-! Actual polynomial-time exponent-vector enumeration for each fixed number
of entry types. Unary input size makes the explicit polynomial output honest. -/
namespace PlanarHom.ExponentVectorMachines
open PlanarHom.Complexity

private theorem fp_unarySuccessor : FP BitEncoding.unaryNat BitEncoding.unaryNat (fun n=>n+1):=by
  have hw:=fp_code_view BitEncoding.unaryNat BitEncoding.bits BitEncoding.unaryNat.encode (fun _=>rfl)
  have h:=((fp_const BitEncoding.unaryNat BitEncoding.bits [true]).pair hw).comp PairProjectionMachines.fp_append
  apply h.transportOutput
  intro n
  rfl

private theorem fp_rangeInclusive : FP BitEncoding.unaryNat BitEncoding.nat.list
    (fun m=>(List.range (m+1)).reverse):=fp_unarySuccessor.comp PlanarHom.UnaryRangeMachines.fp_range

/-- Prefix one fixed numeric coordinate to each previously enumerated vector. -/
private theorem fp_extendOne :
    FP (BitEncoding.nat.prod BitEncoding.nat.list.list) BitEncoding.nat.list.list
      (fun p=>p.2.map (List.cons p.1)):=
  PlanarHom.ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat.list
    BitEncoding.nat.list (fun p=>p.1::p.2) (PlanarHom.ListMutationMachines.fp_cons BitEncoding.nat)

private theorem fp_expand :
    FP (BitEncoding.nat.list.list.prod BitEncoding.nat.list) BitEncoding.nat.list.list
      (fun p=>p.2.flatMap (fun a=>p.1.map (List.cons a))):=by
  have hswap:=(PairProjectionMachines.fp_snd BitEncoding.nat.list.list BitEncoding.nat).pair
    (PairProjectionMachines.fp_fst BitEncoding.nat.list.list BitEncoding.nat)
  have hb:=hswap.comp fp_extendOne
  have hm:=PlanarHom.ListContextMachines.fp_mapWithContext BitEncoding.nat.list.list BitEncoding.nat
    BitEncoding.nat.list.list (fun p=>p.1.map (List.cons p.2)) hb
  exact (hm.comp (PlanarHom.ListFlattenMachines.fp_flatten BitEncoding.nat.list)).congr
    (fun _=>rfl)

/-- Dimension is fixed at compile time. Runtime is polynomial in unary `m`; no
exponential-in-binary-m enumeration is claimed. -/
theorem fp_box (t : ℕ) :
    FP BitEncoding.unaryNat BitEncoding.nat.list.list (PlanarHom.ExponentVectors.box t):=by
  induction t with
  | zero=>exact fp_const _ _ [[]]
  | succ t ih=>
    exact ((ih.pair fp_rangeInclusive).comp fp_expand).congr (fun _=>rfl)

private theorem fp_sumMatches :
    FP (BitEncoding.unaryNat.prod BitEncoding.nat.list) BitEncoding.bool
      (fun p=>decide (p.2.sum=p.1)):=by
  have hm:=(PairProjectionMachines.fp_fst BitEncoding.unaryNat BitEncoding.nat.list).comp
    PlanarHom.UnaryNatConversionMachine.fp_conversion
  have hs:=(PairProjectionMachines.fp_snd BitEncoding.unaryNat BitEncoding.nat.list).comp
    PlanarHom.NatListSumMachines.fp_sum
  exact (hs.pair hm).comp PlanarHom.NatListSumMachines.fp_equal

/-- Exact weak-composition enumeration, including the empty/zero cases. -/
theorem fp_weak (t : ℕ) :
    FP BitEncoding.unaryNat BitEncoding.nat.list.list (PlanarHom.ExponentVectors.weak t):=by
  have h:=((fp_id BitEncoding.unaryNat).pair (fp_box t)).comp
    (PlanarHom.ContextFilterMachines.fp_filterWithContext BitEncoding.unaryNat BitEncoding.nat.list
      (fun p=>decide (p.2.sum=p.1)) fp_sumMatches)
  exact h

end PlanarHom.ExponentVectorMachines
