import PlanarHom.ColoringCrossMacroTypedClause11
noncomputable section
namespace PlanarHom.ColoringCrossMacroTyped
open MultiGraph ThreeColorPaletteCounting ColoringPalettePairCopy
open ColoringPaletteNetwork ColoringExposedPaletteNetwork ColoringMacroNumericCharts
theorem clause_source : ∀ (i : Fin 12) (e : PlanarColoringClause.Edge),
    ColoringMacroNumericCharts.clauseVertexNumber occurrence i (PlanarColoringClause.graph.src e)=
      (ColoringCrossMacroCoordinates.graph.src (edgeNumber (.inl (.inl (i,e))))).val := by
  intro i
  fin_cases i
  · exact clause_source_0
  · exact clause_source_1
  · exact clause_source_2
  · exact clause_source_3
  · exact clause_source_4
  · exact clause_source_5
  · exact clause_source_6
  · exact clause_source_7
  · exact clause_source_8
  · exact clause_source_9
  · exact clause_source_10
  · exact clause_source_11
theorem clause_target : ∀ (i : Fin 12) (e : PlanarColoringClause.Edge),
    ColoringMacroNumericCharts.clauseVertexNumber occurrence i (PlanarColoringClause.graph.dst e)=
      (ColoringCrossMacroCoordinates.graph.dst (edgeNumber (.inl (.inl (i,e))))).val := by
  intro i
  fin_cases i
  · exact clause_target_0
  · exact clause_target_1
  · exact clause_target_2
  · exact clause_target_3
  · exact clause_target_4
  · exact clause_target_5
  · exact clause_target_6
  · exact clause_target_7
  · exact clause_target_8
  · exact clause_target_9
  · exact clause_target_10
  · exact clause_target_11

theorem link_source : ∀ (i : Fin 11) (e : Fin 6),
    number (graph.src (.inl (.inr (i,e))))=ColoringCrossMacroCoordinates.graph.src (edgeNumber (.inl (.inr (i,e)))) := by decide +kernel

theorem link_target : ∀ (i : Fin 11) (e : Fin 6),
    number (graph.dst (.inl (.inr (i,e))))=ColoringCrossMacroCoordinates.graph.dst (edgeNumber (.inl (.inr (i,e)))) := by decide +kernel

theorem copy_source : ∀ (i : Fin 4) (e : (shape i).Edge),
    number (graph.src (.inr ⟨i,e⟩))=ColoringCrossMacroCoordinates.graph.src (edgeNumber (.inr ⟨i,e⟩)) := by decide +kernel

theorem copy_target : ∀ (i : Fin 4) (e : (shape i).Edge),
    number (graph.dst (.inr ⟨i,e⟩))=ColoringCrossMacroCoordinates.graph.dst (edgeNumber (.inr ⟨i,e⟩)) := by decide +kernel

/-- Endpoint-preserving bijections identify the semantic graph with the actual
numeric edge occurrences whose continuous drawing is independently checked. -/
def numericEquiv : IncidenceEquiv graph ColoringCrossMacroCoordinates.graph where
  vertex := number
  edge := edgeNumber
  src_eq := by
    rintro ((⟨i,e⟩ | ⟨i,e⟩) | ⟨i,e⟩)
    · symm
      apply Fin.ext
      change (ColoringMacroNumericCharts.vertexIndex (n := 17) (c := 12) (l := 11) shape
        (.inl (ColoringPaletteNetwork.clauseMap occurrence i (PlanarColoringClause.labels.symm (PlanarColoringClause.graph.src e))))).val=_
      rw [ColoringMacroNumericCharts.vertexIndex_clauseOriginal]
      exact clause_source i e
    · exact (link_source i e).symm
    · exact (copy_source i e).symm
  dst_eq := by
    rintro ((⟨i,e⟩ | ⟨i,e⟩) | ⟨i,e⟩)
    · symm
      apply Fin.ext
      change (ColoringMacroNumericCharts.vertexIndex (n := 17) (c := 12) (l := 11) shape
        (.inl (ColoringPaletteNetwork.clauseMap occurrence i (PlanarColoringClause.labels.symm (PlanarColoringClause.graph.dst e))))).val=_
      rw [ColoringMacroNumericCharts.vertexIndex_clauseOriginal]
      exact clause_target i e
    · exact (link_target i e).symm
    · exact (copy_target i e).symm

theorem coloring_count : ProperColoringPottsReduction.properColoringCount graph 3=
    6*Nat.card (Solutions occurrence) := by
  rw [graph,ColoringExposedPaletteNetwork.coloring_count occurrence left right shape source
    ColoringCrossMacroCore.cover ColoringCrossMacroCore.coherent,ColoringCrossMacroCore.component_count,pow_one]

end PlanarHom.ColoringCrossMacroTyped
