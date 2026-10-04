import PlanarHom.ColoringMacroCrossFramedRetentionCheckRetainedSource
import PlanarHom.ColoringMacroCrossFramedRetentionCheckRetainedTarget
import PlanarHom.ColoringMacroCrossFramedRetentionCheckRowNodup
import PlanarHom.ColoringMacroCrossFramedRetentionCheckRowHostAll
import PlanarHom.ColoringMacroCrossFramedRetentionCheckRowComplete
import PlanarHom.ColoringMacroCrossFramedRetentionCheckRowRotation
import PlanarHom.ColoringMacroCrossFramedRetentionCheckRowRetained
namespace PlanarHom.ColoringMacroFaces.CrossFramed
theorem numericRow_host (v : Fin 1274) (a : Fin 6336) (ha : a∈numericRow v) : host a=v := by
  have hv := row_host_all v
  simp only [Nat.mod_eq_of_lt v.isLt] at hv
  have h := List.all_eq_true.mp hv a ha
  exact of_decide_eq_true h
theorem numericRow_rotation (a : Fin 6336) : (numericRow (host a)).formPerm a=(permutation*IndexedRotationCertificate.flip 3168) a := by
  apply Fin.ext
  rw [rotation_value]
  simpa only [Nat.mod_eq_of_lt a.isLt] using row_rotation a
end PlanarHom.ColoringMacroFaces.CrossFramed
