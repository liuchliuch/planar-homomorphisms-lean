import PlanarHom.FixedRealLemmaA1Statement

/-! These arithmetic clauses are assembled from their actual machines.
The complete LemmaA1Statement, including inversion and general
prescribed-subfield/integer conversion, is assembled in FixedRealLemmaA1.lean. -/
noncomputable section
namespace PlanarHom.FixedRealLemmaA1
open DensePolynomial Complexity RepresentedBit
variable {d e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction d) K]

theorem equality_inFP (basis:PresentationBasis d e K) : (equalityProblem basis).InFP :=
  typedProblem_inFP _ _
    (BitEncoding.prodNormalizer (FixedRealExtension.normalizer d e) (FixedRealExtension.normalizer d e)) _ _
    (FixedRealExtension.equality d e) (FixedRealExtension.fp_equality d e)
    (fun a h=>FixedRealExtension.equality_value_iff basis a.1 a.2 h.1 h.2)

theorem establishedClauses (basis:PresentationBasis d e K) : EstablishedClauses basis where
  addition:=FixedRealExtension.addition_inFP basis
  multiplication:=FixedRealExtension.multiplication_inFP basis
  equality:=equality_inFP basis
  products:=fun _ A=>FixedRealAlphabet.product_inFP basis A
  nonsingularSystems:=FixedRealExtension.linearSystem_inFP basis
  partitionOutputSize:=fun _ _ _ M U w=>
    FixedRealPartitionOutputBounds.exists_polynomial_raw_answer_bound basis M U w

/-- The same closed clauses hold in each fixed finite extension, with its
explicitly constructed tower basis rather than an assumed Q-basis. -/
theorem establishedFiniteExtension (basis:PresentationBasis d e K)
    (E:Type) [Field E] [Algebra K E] [Algebra (RationalFunction d) E]
    [IsScalarTower (RationalFunction d) K E] [FiniteDimensional K E] :
    EstablishedClauses (extensionBasis basis E) := establishedClauses _

/-- A concrete descendant algorithm suffices to close the exact public output
relation. This adapter takes an actual algorithm and its correctness proof as inputs. -/
theorem descent_of_machine {c f:ℕ} {F:Type} [Field F] [Algebra (RationalFunction c) F]
    (source:PresentationBasis d e K) (target:PresentationBasis c f F) (embed:F→+*K)
    (run:FixedRealExtension.Code d e→FixedRealExtension.Code c f)
    (hrun:FP (FixedRealExtension.encoding d e) (FixedRealExtension.encoding c f) run)
    (hcorrect:∀a,FixedRealExtension.Valid d a→∀z:F,FixedRealExtension.value source a=embed z→
      FixedRealExtension.Valid c (run a) ∧ FixedRealExtension.value target (run a)=z) :
    (descentProblem source target embed).InFP := by
  apply typedProblem_inFP _ _ (FixedRealExtension.normalizer d e) _ _ run hrun
  intro a ha
  obtain ⟨z,hz⟩:=ha.2
  obtain ⟨hv,he⟩:=hcorrect a ha.1 z hz
  exact ⟨hv,by rw [he,hz]⟩

end PlanarHom.FixedRealLemmaA1
