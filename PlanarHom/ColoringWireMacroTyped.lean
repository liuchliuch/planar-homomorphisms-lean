import PlanarHom.ColoringMacroNumericCharts
import PlanarHom.ColoringWireMacroCore
import PlanarHom.ColoringWireMacroCoordinates

/-! The exact typed semantics and literal numeric incidence of the wire
coloring macro. Numeric addresses agree with the frozen coordinate/rotation table.
The graph is built from actual clause and palette-copy graphs, not from an
assumed Boolean relation or an unverified graph-coloring oracle. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringWireMacroTyped
open MultiGraph ThreeColorPaletteCounting ColoringPalettePairCopy
open ColoringPaletteNetwork ColoringExposedPaletteNetwork ColoringMacroNumericCharts
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev occurrence := ColoringWireMacroCore.occurrence
abbrev left := ColoringWireMacroCore.left
abbrev right := ColoringWireMacroCore.right

def shape : Fin 2 → Shape := ![.double,.single]
def source : Fin 2 → Fin 5 × Fin 3 := ![(0,1),(1,1)]

def graph := ColoringExposedPaletteNetwork.graph occurrence left right shape source

abbrev Vertex := ColoringExposedPaletteNetwork.Vertex (V := Fin 7) (C := Fin 5) (L := Fin 4) shape
abbrev Edge := ColoringExposedPaletteNetwork.Edge (C := Fin 5) (L := Fin 4) shape

def number : Vertex ≃ Fin 530 :=
  (ColoringMacroNumericCharts.vertexIndex (n := 7) (c := 5) (l := 4) shape).trans
    (finCongr (by decide))

def edgeNumber : Edge ≃ Fin 1313 :=
  (ColoringMacroNumericCharts.edgeIndex (c := 5) (l := 4) shape).trans (finCongr (by decide))

def portVariable (i : Fin 2) : Fin 7 := ⟨i.val,lt_of_lt_of_le i.isLt (by decide)⟩

def boundary (i : Fin 2) : Fin 3 → Vertex :=
  ![ColoringExposedPaletteNetwork.primary shape (portVariable i),
    ColoringExposedPaletteNetwork.grayPort shape i,ColoringExposedPaletteNetwork.blackPort shape i]

def boundaryIds : Fin 2 → Fin 3 → Fin 530 := ![![0,518,517],![1,520,519]]

theorem boundary_number : ∀ i k,number (boundary i k)=boundaryIds i k := by decide +kernel

theorem clause_source : ∀ (i : Fin 5) (e : PlanarColoringClause.Edge),
    ColoringMacroNumericCharts.clauseVertexNumber occurrence i (PlanarColoringClause.graph.src e)=
      (ColoringWireMacroCoordinates.graph.src (edgeNumber (.inl (.inl (i,e))))).val := by decide +kernel

theorem clause_target : ∀ (i : Fin 5) (e : PlanarColoringClause.Edge),
    ColoringMacroNumericCharts.clauseVertexNumber occurrence i (PlanarColoringClause.graph.dst e)=
      (ColoringWireMacroCoordinates.graph.dst (edgeNumber (.inl (.inl (i,e))))).val := by decide +kernel

theorem link_source : ∀ (i : Fin 4) (e : Fin 6),
    number (graph.src (.inl (.inr (i,e))))=ColoringWireMacroCoordinates.graph.src (edgeNumber (.inl (.inr (i,e)))) := by decide +kernel

theorem link_target : ∀ (i : Fin 4) (e : Fin 6),
    number (graph.dst (.inl (.inr (i,e))))=ColoringWireMacroCoordinates.graph.dst (edgeNumber (.inl (.inr (i,e)))) := by decide +kernel

theorem copy_source : ∀ (i : Fin 2) (e : (shape i).Edge),
    number (graph.src (.inr ⟨i,e⟩))=ColoringWireMacroCoordinates.graph.src (edgeNumber (.inr ⟨i,e⟩)) := by decide +kernel

theorem copy_target : ∀ (i : Fin 2) (e : (shape i).Edge),
    number (graph.dst (.inr ⟨i,e⟩))=ColoringWireMacroCoordinates.graph.dst (edgeNumber (.inr ⟨i,e⟩)) := by decide +kernel

/-- Endpoint-preserving bijections identify the semantic graph with the actual
numeric edge occurrences whose continuous drawing is independently checked. -/
def numericEquiv : IncidenceEquiv graph ColoringWireMacroCoordinates.graph where
  vertex := number
  edge := edgeNumber
  src_eq := by
    rintro ((⟨i,e⟩ | ⟨i,e⟩) | ⟨i,e⟩)
    · symm
      apply Fin.ext
      change (ColoringMacroNumericCharts.vertexIndex (n := 7) (c := 5) (l := 4) shape
        (.inl (ColoringPaletteNetwork.clauseMap occurrence i (PlanarColoringClause.labels.symm (PlanarColoringClause.graph.src e))))).val=_
      rw [ColoringMacroNumericCharts.vertexIndex_clauseOriginal]
      exact clause_source i e
    · exact (link_source i e).symm
    · exact (copy_source i e).symm
  dst_eq := by
    rintro ((⟨i,e⟩ | ⟨i,e⟩) | ⟨i,e⟩)
    · symm
      apply Fin.ext
      change (ColoringMacroNumericCharts.vertexIndex (n := 7) (c := 5) (l := 4) shape
        (.inl (ColoringPaletteNetwork.clauseMap occurrence i (PlanarColoringClause.labels.symm (PlanarColoringClause.graph.dst e))))).val=_
      rw [ColoringMacroNumericCharts.vertexIndex_clauseOriginal]
      exact clause_target i e
    · exact (link_target i e).symm
    · exact (copy_target i e).symm

theorem coloring_count : ProperColoringPottsReduction.properColoringCount graph 3=
    6*Nat.card (Solutions occurrence) := by
  rw [graph,ColoringExposedPaletteNetwork.coloring_count occurrence left right shape source
    ColoringWireMacroCore.cover ColoringWireMacroCore.coherent,ColoringWireMacroCore.component_count,pow_one]

end PlanarHom.ColoringWireMacroTyped
