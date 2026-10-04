import PlanarHom.ColoringMacroWireFramedRetentionCheckRetainedSource
import PlanarHom.ColoringMacroWireFramedRetentionCheckRetainedTarget
import PlanarHom.ColoringMacroWireFramedRetentionCheckRowNodup
import PlanarHom.ColoringMacroWireFramedRetentionCheckRowHostAll
import PlanarHom.ColoringMacroWireFramedRetentionCheckRowComplete
import PlanarHom.ColoringMacroWireFramedRetentionCheckRowRotation
import PlanarHom.ColoringMacroWireFramedRetentionCheckRowRetained
namespace PlanarHom.ColoringMacroFaces.WireFramed
theorem numericRow_host (v : Fin 534) (a : Fin 2646) (ha : a∈numericRow v) : host a=v := by
  have hv := row_host_all v
  simp only [Nat.mod_eq_of_lt v.isLt] at hv
  have h := List.all_eq_true.mp hv a ha
  exact of_decide_eq_true h
theorem numericRow_rotation (a : Fin 2646) : (numericRow (host a)).formPerm a=(permutation*IndexedRotationCertificate.flip 1323) a := by
  apply Fin.ext
  rw [rotation_value]
  simpa only [Nat.mod_eq_of_lt a.isLt] using row_rotation a
end PlanarHom.ColoringMacroFaces.WireFramed
