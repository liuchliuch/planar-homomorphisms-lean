import PlanarHom.ColoringCanvasGeometricEuler
import PlanarHom.ColoringEmitterComputedRows
import PlanarHom.RotationRowsEulerTransport

/-! Literal numeric source Euler for the same computed rows used in the
actual geometric/radial queries. No caller-supplied source Euler premise. -/
noncomputable section
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph FinitePermutationCycles ParsimoniousNorOneInThree

theorem computedGeometricRows_euler (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) :
    (compile f).vertices+count (computedGeometricRows f hf hne).facePerm=
      (compile f).edges.length+2*((compile f).toMultiGraph (compile_valid f)).componentCount Finset.univ := by
  have h:=(geometricRows f).transport_euler (compile_incidenceEquiv f hf hne) (geometricRows_euler f hf hne)
  simpa only [Fintype.card_fin] using h

end PlanarHom.ColoringEmitter.Canvas
