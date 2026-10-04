import PlanarHom.ListCodecMachines
import PlanarHom.BoundedUnaryMachines
import PlanarHom.ArithmeticCircuitPrimitives

/-! Explicit unary list lengths, bounded by their materialized input codewords. -/
namespace PlanarHom.ListUnaryLengthMachine
open PlanarHom.Complexity

theorem fp_length {α : Type} (e : BitEncoding α) :
    FP e.list BitEncoding.unaryNat List.length:=by
  have hN : FP e.list BitEncoding.unaryNat (fun xs=>(e.list.encode xs).length):=
    ⟨PlanarHom.InputLengthMachine.computer e.list⟩
  have hn:=PlanarHom.Complexity.ListCodecMachines.fp_length e
  have h:=((hN.pair hn).comp (show FP (BitEncoding.unaryNat.prod BitEncoding.nat)
    BitEncoding.unaryNat (fun p=>min p.1 p.2) from ⟨PlanarHom.BoundedUnaryMachines.computer⟩))
  exact h.congr (fun xs=>min_eq_right (BitEncoding.list_length_le e xs))

end PlanarHom.ListUnaryLengthMachine
