import PlanarHom.ColoringMacroTestFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem parentBound_b0 : ∀ i : Fin 48, parentValue (0+i.val) < 118 := by decide +kernel

private theorem parentBound_b1 : ∀ i : Fin 48, parentValue (48+i.val) < 118 := by decide +kernel

private theorem parentBound_b2 : ∀ i : Fin 22, parentValue (96+i.val) < 118 := by decide +kernel

private theorem parentBound_n0_0 : ∀ i : Fin 96, parentValue (0+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 118) 0 48 48 parentBound_b0 parentBound_b1

private theorem parentBound_n1_0 : ∀ i : Fin 118, parentValue (0+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 118) 0 96 22 parentBound_n0_0 parentBound_b2

theorem parentBound : ∀ i : Fin 118, parentValue i.val < 118 := by
  simpa only [Nat.zero_add] using parentBound_n1_0

end PlanarHom.ColoringMacroFaces.TestFramed
