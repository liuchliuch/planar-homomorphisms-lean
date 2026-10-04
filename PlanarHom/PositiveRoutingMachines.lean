import PlanarHom.RoutingFoldMachines
import PlanarHom.BlockProgramMachines

/-! The complete numeric planarization compiler is a genuine polynomial-time
bit machine, including all intermediate scripts, rails, blocks, and clauses. -/
namespace PlanarHom.PositiveRoutingCompiler
open Complexity ParsimoniousNorOneInThree PositiveBlockProgram
open PairProjectionMachines ArithmeticCircuitPrimitives

/-- Actual serialized formula-to-formula computation on every typed input.
The validity promise is needed only for semantics and planarity, not runtime. -/
theorem fp_compile : FP formulaEncoding formulaEncoding compile := by
  have hn := fp_fst BitEncoding.unaryNat clauseEncoding.list
  have hstart := hn.pair (fp_const formulaEncoding clauseEncoding.list [])
  have hseed : FP formulaEncoding blockSeedEncoding (fun f => (f.1,program f)) :=
    (hstart.pair fp_program).transportOutput (fun _ => rfl)
  exact hseed.comp fp_blockFold

end PlanarHom.PositiveRoutingCompiler
