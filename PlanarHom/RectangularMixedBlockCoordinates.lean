import PlanarHom.ColoredSeriesGadget
import PlanarHom.TypedBipartiteSpectralBlocks

/-! NEW literal rectangular mixed block coordinates. Coefficient signs and
source availability are unrestricted; this is an exact finite sum identity. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.RectangularMixedGadgets
variable {X Y R : Type} [CommSemiring R]

def cross (B : Matrix X Y R) : Matrix (X⊕Y) (X⊕Y) R := Matrix.fromBlocks 0 B B.transpose 0

def onX (K : Matrix X X R) : Matrix (X⊕Y) (X⊕Y) R := Matrix.fromBlocks K 0 0 0

def onY (K : Matrix Y Y R) : Matrix (X⊕Y) (X⊕Y) R := Matrix.fromBlocks 0 0 0 K

def entrySquare {A B : Type} (M : Matrix A B R) : Matrix A B R := fun i j=>M i j^2

variable [Fintype X] [Fintype Y]

theorem threePath_mixed_gram (B : Matrix X Y R) (K : Matrix Y Y R) :
    TwoTerminal.coloredSignature TwoTerminal.threeEdgePath
      (TwoTerminal.seriesMatrices (cross B) (onY K)) (fun _=>1) = onX (B*K*B.transpose) := by
  rw [TwoTerminal.coloredSignature_threeEdgePath]
  simp [cross,onY,onX,Matrix.fromBlocks_multiply]

end PlanarHom.RectangularMixedGadgets
