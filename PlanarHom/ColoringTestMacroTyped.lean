import PlanarHom.ColoringMacroNumericCharts
import PlanarHom.ColoringTestMacroCore
import PlanarHom.ColoringTestMacroCoordinates

/-! The exact typed semantics and literal numeric incidence of the test
coloring macro. Numeric addresses agree with the frozen coordinate/rotation table.
The graph is built from actual clause and palette-copy graphs, not from an
assumed Boolean relation or an unverified graph-coloring oracle. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringTestMacroTyped
open MultiGraph ThreeColorPaletteCounting ColoringPalettePairCopy
open ColoringPaletteNetwork ColoringExposedPaletteNetwork ColoringMacroNumericCharts
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev occurrence := ColoringTestMacroCore.occurrence
abbrev left := ColoringTestMacroCore.left
abbrev right := ColoringTestMacroCore.right

def shape : Fin 3 → Shape := ![.single,.single,.single]
def source : Fin 3 → Fin 1 × Fin 3 := ![(0,1),(0,0),(0,2)]

def graph := ColoringExposedPaletteNetwork.graph occurrence left right shape source

abbrev Vertex := ColoringExposedPaletteNetwork.Vertex (V := Fin 3) (C := Fin 1) (L := Fin 0) shape
abbrev Edge := ColoringExposedPaletteNetwork.Edge (C := Fin 1) (L := Fin 0) shape

def number : Vertex ≃ Fin 114 :=
  (ColoringMacroNumericCharts.vertexIndex (n := 3) (c := 1) (l := 0) shape).trans
    (finCongr (by decide))

def edgeNumber : Edge ≃ Fin 272 :=
  (ColoringMacroNumericCharts.edgeIndex (c := 1) (l := 0) shape).trans (finCongr (by decide))

def portVariable (i : Fin 3) : Fin 3 := ⟨i.val,lt_of_lt_of_le i.isLt (by decide)⟩

def boundary (i : Fin 3) : Fin 3 → Vertex :=
  ![ColoringExposedPaletteNetwork.primary shape (portVariable i),
    ColoringExposedPaletteNetwork.grayPort shape i,ColoringExposedPaletteNetwork.blackPort shape i]

def boundaryIds : Fin 3 → Fin 3 → Fin 114 := ![![0,106,105],![1,108,107],![2,110,109]]

theorem boundary_number : ∀ i k,number (boundary i k)=boundaryIds i k := by decide +kernel

theorem clause_source : ∀ (i : Fin 1) (e : PlanarColoringClause.Edge),
    ColoringMacroNumericCharts.clauseVertexNumber occurrence i (PlanarColoringClause.graph.src e)=
      (ColoringTestMacroCoordinates.graph.src (edgeNumber (.inl (.inl (i,e))))).val := by decide +kernel

theorem clause_target : ∀ (i : Fin 1) (e : PlanarColoringClause.Edge),
    ColoringMacroNumericCharts.clauseVertexNumber occurrence i (PlanarColoringClause.graph.dst e)=
      (ColoringTestMacroCoordinates.graph.dst (edgeNumber (.inl (.inl (i,e))))).val := by decide +kernel

theorem link_source : ∀ (i : Fin 0) (e : Fin 6),
    number (graph.src (.inl (.inr (i,e))))=ColoringTestMacroCoordinates.graph.src (edgeNumber (.inl (.inr (i,e)))) := by decide +kernel

theorem link_target : ∀ (i : Fin 0) (e : Fin 6),
    number (graph.dst (.inl (.inr (i,e))))=ColoringTestMacroCoordinates.graph.dst (edgeNumber (.inl (.inr (i,e)))) := by decide +kernel

theorem copy_source : ∀ (i : Fin 3) (e : (shape i).Edge),
    number (graph.src (.inr ⟨i,e⟩))=ColoringTestMacroCoordinates.graph.src (edgeNumber (.inr ⟨i,e⟩)) := by decide +kernel

theorem copy_target : ∀ (i : Fin 3) (e : (shape i).Edge),
    number (graph.dst (.inr ⟨i,e⟩))=ColoringTestMacroCoordinates.graph.dst (edgeNumber (.inr ⟨i,e⟩)) := by decide +kernel

/-- Endpoint-preserving bijections identify the semantic graph with the actual
numeric edge occurrences whose continuous drawing is independently checked. -/
def numericEquiv : IncidenceEquiv graph ColoringTestMacroCoordinates.graph where
  vertex := number
  edge := edgeNumber
  src_eq := by
    rintro ((⟨i,e⟩ | ⟨i,e⟩) | ⟨i,e⟩)
    · symm
      apply Fin.ext
      change (ColoringMacroNumericCharts.vertexIndex (n := 3) (c := 1) (l := 0) shape
        (.inl (ColoringPaletteNetwork.clauseMap occurrence i (PlanarColoringClause.labels.symm (PlanarColoringClause.graph.src e))))).val=_
      rw [ColoringMacroNumericCharts.vertexIndex_clauseOriginal]
      exact clause_source i e
    · exact (link_source i e).symm
    · exact (copy_source i e).symm
  dst_eq := by
    rintro ((⟨i,e⟩ | ⟨i,e⟩) | ⟨i,e⟩)
    · symm
      apply Fin.ext
      change (ColoringMacroNumericCharts.vertexIndex (n := 3) (c := 1) (l := 0) shape
        (.inl (ColoringPaletteNetwork.clauseMap occurrence i (PlanarColoringClause.labels.symm (PlanarColoringClause.graph.dst e))))).val=_
      rw [ColoringMacroNumericCharts.vertexIndex_clauseOriginal]
      exact clause_target i e
    · exact (link_target i e).symm
    · exact (copy_target i e).symm

theorem coloring_count : ProperColoringPottsReduction.properColoringCount graph 3=
    6*Nat.card (Solutions occurrence) := by
  rw [graph,ColoringExposedPaletteNetwork.coloring_count occurrence left right shape source
    ColoringTestMacroCore.cover ColoringTestMacroCore.coherent,ColoringTestMacroCore.component_count,pow_one]

end PlanarHom.ColoringTestMacroTyped
