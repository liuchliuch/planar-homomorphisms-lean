import PlanarHom.RectangularWalshCoordinates

/-! Exact surviving physical-gadget definitions extracted from recovered
RectangularPhysicalSourceForm. The original consumer can import these shared
constants once its mixed Walsh classification dependency is supplied. -/
noncomputable section
namespace PlanarHom.RectangularWalshConvolution

/-- Literal matrix view used by the recovered noise-scaling consumer. -/
def tensorMatrix {d:ℕ} (ρ:Fin d→ℝ):Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ:=Boolean.tensor ρ

def parallelSquare {a b:ℕ} (B:Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ) (t:ℝ):
    Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ:=
  fun x y=>((noiseMatrix (d:=a) t*B:Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ)) x y*
    ((noiseMatrix (d:=a) t*B:Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ)) x y

def parallelSquareGram {a b:ℕ} (B:Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ) (t:ℝ):
    Matrix (Boolean.Cube a) (Boolean.Cube a) ℝ:=parallelSquare B t*(parallelSquare B t).transpose

theorem physicalGram_source {d:ℕ} (B:Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ) (t:ℝ):
    physicalGram (sourceCoefficients B) t=((2:ℝ)^d)⁻¹^2 • parallelSquareGram B t:=by
  have h:squaredNoise (sourceCoefficients B) t=parallelSquare B t:=by
    funext x y
    change noiseValues (sourceCoefficients B) t x y*noiseValues (sourceCoefficients B) t x y=_
    rw [source_noise_matrix]
    rfl
  rw [physicalGram,h,parallelSquareGram]

end PlanarHom.RectangularWalshConvolution
