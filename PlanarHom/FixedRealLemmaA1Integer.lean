import PlanarHom.FixedRealLemmaA1Arithmetic
import PlanarHom.FixedRealIntegerExtraction

/-! Ordinary integer output is an actual bit program, independent of the
general prescribed-subfield conversion theorem. -/
noncomputable section
namespace PlanarHom.FixedRealLemmaA1
open DensePolynomial Complexity RepresentedBit
variable {d e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction d) K]

theorem integer_inFP (basis:PresentationBasis d e K) : (integerProblem basis).InFP := by
  apply typedProblem_inFP _ _ (FixedRealExtension.normalizer d e) _ _
    (FixedRealIntegerExtraction.extractInteger basis) (FixedRealIntegerExtraction.fp_extractInteger basis)
  intro a ha
  obtain ⟨z,hz⟩:=ha.2
  rw [FixedRealIntegerExtraction.extractInteger_value basis a ha.1 z hz]
  exact hz

end PlanarHom.FixedRealLemmaA1
