import PlanarHom.ColoringMacroNumericCharts
import PlanarHom.ColoringCrossMacroCore
import PlanarHom.ColoringCrossMacroCoordinates

/-! The exact typed semantics and literal numeric incidence of the cross
coloring macro. Numeric addresses agree with the frozen coordinate/rotation table.
The graph is built from actual clause and palette-copy graphs, not from an
assumed Boolean relation or an unverified graph-coloring oracle. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringCrossMacroTyped
open MultiGraph ThreeColorPaletteCounting ColoringPalettePairCopy
open ColoringPaletteNetwork ColoringExposedPaletteNetwork ColoringMacroNumericCharts
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev occurrence := ColoringCrossMacroCore.occurrence
abbrev left := ColoringCrossMacroCore.left
abbrev right := ColoringCrossMacroCore.right

def shape : Fin 4 → Shape := ![.single,.single,.double,.double]
def source : Fin 4 → Fin 12 × Fin 3 := ![(0,2),(3,0),(4,0),(7,1)]

def graph := ColoringExposedPaletteNetwork.graph occurrence left right shape source

abbrev Vertex := ColoringExposedPaletteNetwork.Vertex (V := Fin 17) (C := Fin 12) (L := Fin 11) shape
abbrev Edge := ColoringExposedPaletteNetwork.Edge (C := Fin 12) (L := Fin 11) shape

def number : Vertex ≃ Fin 1270 :=
  (ColoringMacroNumericCharts.vertexIndex (n := 17) (c := 12) (l := 11) shape).trans
    (finCongr (by decide))

def edgeNumber : Edge ≃ Fin 3152 :=
  (ColoringMacroNumericCharts.edgeIndex (c := 12) (l := 11) shape).trans (finCongr (by decide))

def portVariable (i : Fin 4) : Fin 17 := ⟨i.val,lt_of_lt_of_le i.isLt (by decide)⟩

def boundary (i : Fin 4) : Fin 3 → Vertex :=
  ![ColoringExposedPaletteNetwork.primary shape (portVariable i),
    ColoringExposedPaletteNetwork.grayPort shape i,ColoringExposedPaletteNetwork.blackPort shape i]

def boundaryIds : Fin 4 → Fin 3 → Fin 1270 := ![![0,1242,1241],![1,1244,1243],![2,1246,1245],![3,1248,1247]]

theorem boundary_number : ∀ i k,number (boundary i k)=boundaryIds i k := by decide +kernel


end PlanarHom.ColoringCrossMacroTyped
