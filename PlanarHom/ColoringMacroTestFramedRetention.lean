import PlanarHom.ColoringMacroTestFramedRetentionCheckRetainedSource
import PlanarHom.ColoringMacroTestFramedRetentionCheckRetainedTarget
import PlanarHom.ColoringMacroTestFramedRetentionCheckRowNodup
import PlanarHom.ColoringMacroTestFramedRetentionCheckRowHostAll
import PlanarHom.ColoringMacroTestFramedRetentionCheckRowComplete
import PlanarHom.ColoringMacroTestFramedRetentionCheckRowRotation
import PlanarHom.ColoringMacroTestFramedRetentionCheckRowRetained
namespace PlanarHom.ColoringMacroFaces.TestFramed
theorem numericRow_host (v : Fin 118) (a : Fin 570) (ha : a∈numericRow v) : host a=v := by
  have hv := row_host_all v
  simp only [Nat.mod_eq_of_lt v.isLt] at hv
  have h := List.all_eq_true.mp hv a ha
  exact of_decide_eq_true h
theorem numericRow_rotation (a : Fin 570) : (numericRow (host a)).formPerm a=(permutation*IndexedRotationCertificate.flip 285) a := by
  apply Fin.ext
  rw [rotation_value]
  simpa only [Nat.mod_eq_of_lt a.isLt] using row_rotation a
end PlanarHom.ColoringMacroFaces.TestFramed
