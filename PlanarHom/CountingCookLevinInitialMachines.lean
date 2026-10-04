import PlanarHom.CountingCookLevinStateIndex
import PlanarHom.RawBooleanListMachine
import PlanarHom.OccurrencePfaffianListPrimitives
import PlanarHom.ConditionalMachines

/-! Genuine raw-input machines for the input-dependent initial Boolean wires. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic Complexity PairProjectionMachines

/-- A binary-index raw-input lookup, charging the actual bit word and index. -/
theorem fp_rawBitAt : FP (BitEncoding.bits.prod BitEncoding.nat) BitEncoding.bool
    (fun p => p.1[p.2]?.getD false) := by
  exact ((RawBooleanListMachine.fp_boolList.prodMap (fp_id BitEncoding.nat)).comp
    (PfaffianList.fp_at BitEncoding.bool false))

def initialHeadTest (m : Machine) (a : m.Γ) (x : Bits) : Bool :=
  if x.length=0 then decide (m.blank=a) else decide (m.input (x.headD false)=a)

theorem fp_initialHeadTest (m : Machine) (a : m.Γ) :
    FP BitEncoding.bits BitEncoding.bool (initialHeadTest m a) := by
  have hn : FP BitEncoding.bits BitEncoding.nat (fun x : Bits => x.length) :=
    (show FP BitEncoding.bits BitEncoding.unaryNat (fun x : Bits => x.length) from
      ⟨InputLengthMachine.computer BitEncoding.bits⟩).comp UnaryNatConversionMachine.fp_conversion
  have hz := hn.comp RationalCircuits.fp_nat_isZero
  have hh := RawBooleanListMachine.fp_boolList.comp (ListDecompositionMachines.fp_headD BitEncoding.bool false)
  have hv := hh.comp (ArithmeticCircuitPrimitives.fp_bool_unary BitEncoding.bool (fun b => decide (m.input b=a)))
  exact hz.ite (fp_const BitEncoding.bits BitEncoding.bool (decide (m.blank=a))) hv

theorem initialHeadTest_correct (m : Machine) (a : m.Γ) (x : Bits) :
    initialHeadTest m a x=decide ((initial m x).1.2=a) := by
  cases x <;> simp [initialHeadTest,initial,List.headD]

def initialCellTest (m : Machine) (a : Option m.Γ) (p : Bits × (Bool × ℕ)) : Bool :=
  if p.2.1 then decide (none=a) else
    if p.2.2+1<p.1.length then decide (some (m.input (p.1[p.2.2+1]?.getD false))=a)
    else decide (none=a)

theorem fp_initialCellTest (m : Machine) (a : Option m.Γ) :
    FP (BitEncoding.bits.prod (BitEncoding.bool.prod BitEncoding.nat)) BitEncoding.bool (initialCellTest m a) := by
  let ein := BitEncoding.bits.prod (BitEncoding.bool.prod BitEncoding.nat)
  have hx := fp_fst BitEncoding.bits (BitEncoding.bool.prod BitEncoding.nat)
  have hp := fp_snd BitEncoding.bits (BitEncoding.bool.prod BitEncoding.nat)
  have hs := hp.comp (fp_fst BitEncoding.bool BitEncoding.nat)
  have hi := hp.comp (fp_snd BitEncoding.bool BitEncoding.nat)
  have hin := hi.comp BinaryArithmetic.fp_successor
  have hn : FP ein BitEncoding.nat (fun p : Bits × (Bool × ℕ) => p.1.length) :=
    (hx.comp (show FP BitEncoding.bits BitEncoding.unaryNat (fun x : Bits => x.length) from
      ⟨InputLengthMachine.computer BitEncoding.bits⟩)).comp UnaryNatConversionMachine.fp_conversion
  have hlt := (hin.pair hn).comp BinaryArithmetic.fp_comparison
  have hb := (hx.pair hin).comp fp_rawBitAt
  have hv := hb.comp (ArithmeticCircuitPrimitives.fp_bool_unary BitEncoding.bool
    (fun b => decide (some (m.input b)=a)))
  have hz := fp_const ein BitEncoding.bool (decide (none=a))
  have hright := hlt.ite hv hz
  exact (hs.pair (hz.pair hright)).comp (ConditionalMachines.fp_select BitEncoding.bool)

/-- Initial tape-cell tests correspond to the literal list representatives. -/
theorem initialCellTest_correct (m : Machine) (a : Option m.Γ) (x : Bits) (side : Bool) (i : ℕ) :
    initialCellTest m a (x,(side,i)) =
      decide ((if side then (initial m x).2.1 else (initial m x).2.2)[i]?=a) := by
  cases side
  · simp only [initialCellTest,Bool.false_eq_true,↓reduceIte,initial,List.getElem?_tail,List.getElem?_map]
    by_cases hi : i+1<x.length
    · rw [if_pos hi,List.getElem?_eq_getElem hi]
      simp
    · rw [if_neg hi,List.getElem?_eq_none (by omega)]
      rfl
  · simp [initialCellTest,initial]

end PlanarHom.CountingCookLevin
