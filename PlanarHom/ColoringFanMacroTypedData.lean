import PlanarHom.ColoringMacroNumericCharts
import PlanarHom.ColoringFanMacroCore
import PlanarHom.ColoringFanMacroCoordinates

/-! The exact typed semantics and literal numeric incidence of the fan
coloring macro. Numeric addresses agree with the frozen coordinate/rotation table.
The graph is built from actual clause and palette-copy graphs, not from an
assumed Boolean relation or an unverified graph-coloring oracle. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringFanMacroTyped
open MultiGraph ThreeColorPaletteCounting ColoringPalettePairCopy
open ColoringPaletteNetwork ColoringExposedPaletteNetwork ColoringMacroNumericCharts
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev occurrence := ColoringFanMacroCore.occurrence
abbrev left := ColoringFanMacroCore.left
abbrev right := ColoringFanMacroCore.right

def shape : Fin 3 → Shape := ![.double,.single,.single]
def source : Fin 3 → Fin 10 × Fin 3 := ![(5,1),(1,0),(6,1)]

def graph := ColoringExposedPaletteNetwork.graph occurrence left right shape source

abbrev Vertex := ColoringExposedPaletteNetwork.Vertex (V := Fin 13) (C := Fin 10) (L := Fin 9) shape
abbrev Edge := ColoringExposedPaletteNetwork.Edge (C := Fin 10) (L := Fin 9) shape

def number : Vertex ≃ Fin 1054 :=
  (ColoringMacroNumericCharts.vertexIndex (n := 13) (c := 10) (l := 9) shape).trans
    (finCongr (by decide))

def edgeNumber : Edge ≃ Fin 2619 :=
  (ColoringMacroNumericCharts.edgeIndex (c := 10) (l := 9) shape).trans (finCongr (by decide))

def portVariable (i : Fin 3) : Fin 13 := ⟨i.val,lt_of_lt_of_le i.isLt (by decide)⟩

def boundary (i : Fin 3) : Fin 3 → Vertex :=
  ![ColoringExposedPaletteNetwork.primary shape (portVariable i),
    ColoringExposedPaletteNetwork.grayPort shape i,ColoringExposedPaletteNetwork.blackPort shape i]

def boundaryIds : Fin 3 → Fin 3 → Fin 1054 := ![![0,1034,1033],![1,1036,1035],![2,1038,1037]]

theorem boundary_number : ∀ i k,number (boundary i k)=boundaryIds i k := by decide +kernel


end PlanarHom.ColoringFanMacroTyped
