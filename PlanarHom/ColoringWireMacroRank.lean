import PlanarHom.ColoringWireMacroSpatialData
noncomputable section
namespace PlanarHom.ColoringWireMacroCoordinates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rank_point : ∀ v,coordinateRank (point v)=v := by
  intro v
  fin_cases v <;> rfl
end PlanarHom.ColoringWireMacroCoordinates
