import PlanarHom.FisherInheritedRowProgram

/-! NEW total Fisher compiler parameterized by the supplied rotation rows.
It never replaces the supplied surface rotation with a computed planar one. -/
namespace PlanarHom.SurfaceFisherCode
open Complexity
abbrev Rows := PlanarityRowFaceCode.Rows

def orderRows (rows : Rows) : Rows := rows.map (List.map PlanarityRotationCode.reverse)
def intermediate (g : MixedCode) (rows : Rows) : MixedCode := FisherExpansionCode.code g (orderRows rows)
def code (g : MixedCode) (rows : Rows) : MixedCode := FisherCubicCode.code (intermediate g rows)
def expansionRows (g : MixedCode) (rows : Rows) : Rows :=
  (List.range (intermediate g rows).vertices).map (FisherInheritedRowCode.expansionRow g (orderRows rows))
def inheritedRows (g : MixedCode) (rows : Rows) : Rows :=
  (List.range (code g rows).vertices).map (FisherInheritedRowCode.cubicRow (intermediate g rows) (expansionRows g rows))
def orientationLog (g : MixedCode) (rows : Rows) : List ℕ :=
  PlanarityRowFaceCode.orientationLog (code g rows) (inheritedRows g rows)

end PlanarHom.SurfaceFisherCode
