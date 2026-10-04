import PlanarHom.FixedRealLemmaA1Established
import PlanarHom.FixedExtensionInverseRepresented

/-! Complete arithmetic and output-size clauses of Lemma A.1, including actual
inversion. General prescribed-subfield descent remains independently tracked
until its compatible-presentation construction and runtime composition close. -/
noncomputable section
namespace PlanarHom.FixedRealLemmaA1
open DensePolynomial Complexity
variable {d e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction d) K]

theorem inversion (basis:PresentationBasis d e K) : Inversion basis := by
  refine ⟨FixedRealExtension.inverse (FixedRealExtension.multiplicationTable basis)
    (FixedRealExtension.oneCode basis),FixedRealExtension.fp_inverse _ _,?_⟩
  intro a ha hn
  exact ⟨FixedRealExtension.inverse_valid basis _ (FixedRealExtension.multiplicationTable_realizes basis)
    _ a (FixedRealExtension.oneCode_valid basis) ha,
    FixedRealExtension.inverse_value basis _ (FixedRealExtension.multiplicationTable_realizes basis)
      _ a (FixedRealExtension.oneCode_valid basis) (FixedRealExtension.oneCode_value basis) ha⟩

theorem arithmeticClauses (basis:PresentationBasis d e K) : ArithmeticClauses basis where
  toEstablishedClauses:=establishedClauses basis
  inversion:=inversion basis

theorem arithmeticFiniteExtension (basis:PresentationBasis d e K)
    (E:Type) [Field E] [Algebra K E] [Algebra (RationalFunction d) E]
    [IsScalarTower (RationalFunction d) K E] [FiniteDimensional K E] :
    ArithmeticClauses (extensionBasis basis E) := arithmeticClauses _

end PlanarHom.FixedRealLemmaA1
