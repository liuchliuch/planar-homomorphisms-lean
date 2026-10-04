import PlanarHom.ColoringMacroFanFramedRetentionCheckRetainedSource
import PlanarHom.ColoringMacroFanFramedRetentionCheckRetainedTarget
import PlanarHom.ColoringMacroFanFramedRetentionCheckRowNodup
import PlanarHom.ColoringMacroFanFramedRetentionCheckRowHostAll
import PlanarHom.ColoringMacroFanFramedRetentionCheckRowComplete
import PlanarHom.ColoringMacroFanFramedRetentionCheckRowRotation
import PlanarHom.ColoringMacroFanFramedRetentionCheckRowRetained
namespace PlanarHom.ColoringMacroFaces.FanFramed
theorem numericRow_host (v : Fin 1058) (a : Fin 5264) (ha : a∈numericRow v) : host a=v := by
  have hv := row_host_all v
  simp only [Nat.mod_eq_of_lt v.isLt] at hv
  have h := List.all_eq_true.mp hv a ha
  exact of_decide_eq_true h
theorem numericRow_rotation (a : Fin 5264) : (numericRow (host a)).formPerm a=(permutation*IndexedRotationCertificate.flip 2632) a := by
  apply Fin.ext
  rw [rotation_value]
  simpa only [Nat.mod_eq_of_lt a.isLt] using row_rotation a
end PlanarHom.ColoringMacroFaces.FanFramed
