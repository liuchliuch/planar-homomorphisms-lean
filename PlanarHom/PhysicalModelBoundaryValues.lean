import PlanarHom.ClockMatrixObstruction
import PlanarHom.BlumeCapelMatrix
import PlanarHom.CoupledIsingActualQuotient
import PlanarHom.RankOne

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PhysicalModels
variable {V E C:Type} [Fintype V] [Fintype E] [Fintype C]

theorem all_ones_partition (G:MultiGraph V E) (w:C→ℝ) :
    G.partition (fun _ _=>1) w=(∑i,w i)^Fintype.card V := by
  simpa using G.partition_rankOne (fun _=>1) w

theorem clock_zero_partition (G:MultiGraph V E) (q:ℕ) (w:Fin q→ℝ) :
    G.partition (ClockModel.interaction q 0) w=(∑i,w i)^Fintype.card V := by
  rw [ClockModel.zero_interaction]
  exact all_ones_partition G w

theorem blumeCapel_zero_partition (G:MultiGraph V E) (D F:ℝ) :
    G.partition (BlumeCapel.interaction 0) (BlumeCapel.weight D F)=
      (∑i,BlumeCapel.weight D F i)^Fintype.card V := by
  rw [BlumeCapel.zero_interaction]
  exact all_ones_partition G _

theorem coupled_empty_interaction (n:ℕ) (a:Fin 0→BinaryCharacters.Space n) (J:Fin 0→ℝ) :
    CoupledIsing.interaction a J=fun _ _=>1 := by
  ext x y
  simp [CoupledIsing.interaction,BinaryCharacters.interaction,BinaryCharacters.kernel]

theorem coupled_empty_partition (G:MultiGraph V E) (n:ℕ) (a:Fin 0→BinaryCharacters.Space n)
    (J:Fin 0→ℝ) (w:BinaryCharacters.Space n→ℝ) :
    G.partition (CoupledIsing.interaction a J) w=(∑i,w i)^Fintype.card V := by
  rw [coupled_empty_interaction]
  exact all_ones_partition G w

end PlanarHom.PhysicalModels
