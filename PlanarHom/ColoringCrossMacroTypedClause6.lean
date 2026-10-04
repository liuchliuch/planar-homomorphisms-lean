import PlanarHom.ColoringCrossMacroTypedClause5
noncomputable section
namespace PlanarHom.ColoringCrossMacroTyped
open MultiGraph ThreeColorPaletteCounting ColoringPalettePairCopy
open ColoringPaletteNetwork ColoringExposedPaletteNetwork ColoringMacroNumericCharts
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clause_source_6 : ∀ (e : PlanarColoringClause.Edge),
    ColoringMacroNumericCharts.clauseVertexNumber occurrence 6 (PlanarColoringClause.graph.src e)=
      (ColoringCrossMacroCoordinates.graph.src (edgeNumber (.inl (.inl (6,e))))).val := by decide +kernel
theorem clause_target_6 : ∀ (e : PlanarColoringClause.Edge),
    ColoringMacroNumericCharts.clauseVertexNumber occurrence 6 (PlanarColoringClause.graph.dst e)=
      (ColoringCrossMacroCoordinates.graph.dst (edgeNumber (.inl (.inl (6,e))))).val := by decide +kernel
end PlanarHom.ColoringCrossMacroTyped
