import PlanarHom.MarkedOccurrenceCount
import PlanarHom.BoundedUnaryMachines

/-! An actual unary selected-occurrence count, polynomial in the graph input. -/
namespace PlanarHom.Complexity.MixedCode
open Turing PlanarHom.MachineComposition PlanarHom.MachinePairing

/-- The numeric output is bounded by the graph's explicit edge list. Its unary
expansion is implemented using an actual input-length cap and bounded converter. -/
noncomputable def unaryMarkedCountComputer (selected : ℕ) :
    TM2ComputableInPolyTime encoding.toFinEncoding BitEncoding.unaryNat.toFinEncoding
      (markedCount selected):=by
  let paired:=pairComputers (PlanarHom.InputLengthMachine.computer encoding) (markedCountComputer selected)
  let result:=composeComputers paired PlanarHom.BoundedUnaryMachines.computer
  change TM2ComputableInPolyTime encoding.toFinEncoding BitEncoding.unaryNat.toFinEncoding
    (fun g=>min (encoding.encode g).length (g.markedCount selected)) at result
  have he : (fun g : MixedCode=>min (encoding.encode g).length (g.markedCount selected))=
      markedCount selected:=by
    funext g
    exact min_eq_right (markedCount_le_input selected g)
  rw [he] at result
  exact result

theorem fp_unaryMarkedCount (selected : ℕ) :
    FP encoding BitEncoding.unaryNat (markedCount selected):=⟨unaryMarkedCountComputer selected⟩

end PlanarHom.Complexity.MixedCode
