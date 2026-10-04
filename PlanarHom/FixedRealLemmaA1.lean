import PlanarHom.FixedRealLemmaA1Integer
import PlanarHom.GeneralFixedSubfieldDescent

/-! Lemma A.1, with its complete prescribed-field scope. Every runtime witness
is constructed by the imported actual bit programs. General subfield descent,
ordinary integer output, and fixed finite algebraic extensions are included;
no arithmetic capability or descendant converter is an assumption. -/
noncomputable section
namespace PlanarHom.FixedRealLemmaA1
open DensePolynomial Complexity RepresentedBit
variable {d e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction d) K]

theorem prescribedSubfieldDescent (basis:PresentationBasis d e K) : PrescribedSubfieldDescent basis := by
  intro c f F hF hAF target embed
  obtain ⟨run,hrun,hcorrect⟩:=GeneralFixedSubfieldDescent.exists_conversion basis target embed
  exact descent_of_machine basis target embed run hrun hcorrect

theorem completeFieldClauses (basis:PresentationBasis d e K) : CompleteFieldClauses basis :=
  ⟨arithmeticClauses basis,prescribedSubfieldDescent basis,integer_inFP basis⟩

theorem finiteExtensionClauses (basis:PresentationBasis d e K) : FiniteExtensionClauses basis := by
  intro E hE hKE hRE hTower hfinite
  exact completeFieldClauses (extensionBasis basis E)

/-- Exact Lemma A.1: fixed products, nonsingular systems, exact output-size
existence, finite algebraic extensions, prescribed-subfield output conversion,
and ordinary integer extraction. No numerical real-order oracle is used. -/
theorem lemmaA1 (basis:PresentationBasis d e K) : LemmaA1Statement basis :=
  ⟨completeFieldClauses basis,finiteExtensionClauses basis⟩

end PlanarHom.FixedRealLemmaA1
