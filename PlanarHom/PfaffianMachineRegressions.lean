import PlanarHom.OccurrencePfaffianProgramBridge
import PlanarHom.OccurrenceSkewCodeSemantics

/-! NEW reconstructed regression proofs and executable checks. No native
proof evaluation or trusted evaluator axiom is used. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace ReimplementedPfaffianMachine
open PlanarHom.PfaffianList PlanarHom.MultiGraph.PfaffianElimination

 theorem empty_value : evaluateGrid ([] : Grid ℚ) = 1 := rfl

 theorem negative_pair :
    evaluateGrid (matrixRows (![![(0:ℚ),-3],![3,0]] : Matrix (Fin 2) (Fin 2) ℚ)) = -3 := by
  rw [evaluateGrid_eq_elimination _
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)]
  change evaluate _ [0,1] = -3
  rw [evaluate_pair]
  rfl

 theorem fractional_pair :
    evaluateGrid (matrixRows (![![(0:ℚ),2/3],![-2/3,0]] : Matrix (Fin 2) (Fin 2) ℚ)) = 2/3 := by
  rw [evaluateGrid_eq_elimination _
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)]
  change evaluate _ [0,1] = 2/3
  rw [evaluate_pair]
  rfl

 theorem skipped_pivot :
    evaluateGrid (matrixRows
      (![![(0:ℚ),0,2,-3],![0,0,5,7],![-2,-5,0,11],![3,-7,-11,0]] : Matrix (Fin 4) (Fin 4) ℚ)) = -29 := by
  rw [evaluateGrid_eq_elimination _
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)]
  exact signed_four_vertex_regression

 theorem total_termination (g : Grid ℚ) :
    (step^[g.length] (initialState g)).2.1 = [] := evaluateRawGrid_terminated g

 theorem terminal_stability (g : Grid ℚ) (n : ℕ) :
    (step^[g.length+n] (initialState g)).2.2 = evaluateRawGrid g := evaluateRawGrid_stable g n

-- Compiler execution checks for raw lists, including malformed inputs.
#eval evaluateGrid ([] : Grid ℚ)
#eval evaluateGrid ([[0]] : Grid ℚ)
#eval evaluateGrid ([[0,0],[0,0]] : Grid ℚ)
#eval evaluateGrid ([[0,-3],[3,0]] : Grid ℚ)
#eval evaluateGrid ([[0,2/3],[-2/3,0]] : Grid ℚ)
#eval evaluateGrid ([[0,0,2,-3],[0,0,5,7],[-2,-5,0,11],[3,-7,-11,0]] : Grid ℚ)
#eval evaluateGrid ([[0,1,2],[-1,0,3],[-2,-3,0]] : Grid ℚ)
#eval evaluateGrid ([[0,2,0,0,0,0],[-2,0,0,0,0,0],
  [0,0,0,-3,0,0],[0,0,3,0,0,0],[0,0,0,0,0,5],[0,0,0,0,-5,0]] : Grid ℚ)
#eval evaluateGrid ([[],[]] : Grid ℚ)
#eval evaluateGrid ([[7,2],[999,8]] : Grid ℚ)


def parallelData (log : List ℕ) : PlanarHom.OccurrenceSkewCode.Data ℚ :=
  (⟨2,[(0,(1,0)),(0,(1,0)),(1,(0,0)),(0,(0,0))],[]⟩,(log,[2,-3,5,7]))

#eval evaluateGrid (PlanarHom.OccurrenceSkewCode.grid (parallelData []))
#eval evaluateGrid (PlanarHom.OccurrenceSkewCode.grid (parallelData [1]))
#eval evaluateGrid (PlanarHom.OccurrenceSkewCode.grid (parallelData [1,1]))
#eval PlanarHom.MultiGraph.Kasteleyn.logOrientation [1,1] 1
#eval PlanarHom.MultiGraph.Kasteleyn.logOrientation [1] 1

end ReimplementedPfaffianMachine
