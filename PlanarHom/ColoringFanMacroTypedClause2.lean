import PlanarHom.ColoringFanMacroTypedClause1
noncomputable section
namespace PlanarHom.ColoringFanMacroTyped
open MultiGraph ThreeColorPaletteCounting ColoringPalettePairCopy
open ColoringPaletteNetwork ColoringExposedPaletteNetwork ColoringMacroNumericCharts
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clause_source_2 : ∀ (e : PlanarColoringClause.Edge),
    ColoringMacroNumericCharts.clauseVertexNumber occurrence 2 (PlanarColoringClause.graph.src e)=
      (ColoringFanMacroCoordinates.graph.src (edgeNumber (.inl (.inl (2,e))))).val := by decide +kernel
theorem clause_target_2 : ∀ (e : PlanarColoringClause.Edge),
    ColoringMacroNumericCharts.clauseVertexNumber occurrence 2 (PlanarColoringClause.graph.dst e)=
      (ColoringFanMacroCoordinates.graph.dst (edgeNumber (.inl (.inl (2,e))))).val := by decide +kernel
end PlanarHom.ColoringFanMacroTyped
