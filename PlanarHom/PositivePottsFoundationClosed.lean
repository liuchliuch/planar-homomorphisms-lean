import PlanarHom.PottsCanvasEulerJoin
import PlanarHom.ColoringEmitterGeometricEuler

/-! NEW closed all-q positive Potts foundation. The literal numeric canvas
Euler theorem is proved from the actual source drawing and row programs;
all coefficient, parallel-query, recovery and field-conversion machines are
already consumed by the source reduction. No source or hardness premise remains. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage

theorem positivePottsFoundation : PositivePottsFoundation :=
  PottsCanvasEulerJoin.positivePottsFoundation_of_euler
    (fun f hf hne=>ColoringEmitter.Canvas.computedGeometricRows_euler f hf hne)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
