import PlanarHom.FixedExtensionSystemRepresented
import PlanarHom.FixedRealAlphabetPresentation
import PlanarHom.FixedRealRawOutputBounds
import PlanarHom.FixedRealExtensionEquality
import Mathlib.RingTheory.AlgebraTower

/-! Exact clause inventory for Lemma A.1. A fixed presentation is any finite
basis over a fixed rational-function field, which includes the paper's power
basis. The descent and ordinary-integer clauses are definitions of the required
conclusions, never runtime assumptions or substitute axioms. -/
noncomputable section
namespace PlanarHom.FixedRealLemmaA1
open DensePolynomial Complexity RepresentedBit
variable {d e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction d) K]

/-- The fixed source field, including all background and constraint weights,
uses this prescribed noncanonical dense coordinate presentation. -/
abbrev PresentationBasis (d e:ℕ) (K:Type) [Field K] [Algebra (RationalFunction d) K] :=
  Module.Basis (Fin e) (RationalFunction d) K

def ProductProblem (basis:PresentationBasis d e K) {t:ℕ} (A:Fin t→K) : Problem :=
  (FixedRealExtension.presentation basis).problem (FixedRealAlphabet.symbolEncoding t).list
    (fun _=>True) (fun xs=>(xs.map A).prod)

def PartitionOutputBound (basis:PresentationBasis d e K) : Prop :=
  ∀q bt ut:ℕ,∀M:Fin bt→Matrix (Fin q) (Fin q) K,∀U:Fin ut→Fin q→K,∀w:Fin q→K,
    ∃P:Polynomial ℕ,∀raw:Bits,∀g:MixedCode,MixedCode.encoding.decode raw=some g→
      ∀hg:g.Valid bt ut,∃out:Bits,
        (FixedRealExtension.presentation basis).Represents out (g.evaluate hg M U w) ∧
          out.length≤P.eval raw.length

def Inversion (basis:PresentationBasis d e K) : Prop :=
  ∃run:FixedRealExtension.Code d e→FixedRealExtension.Code d e,
    FP (FixedRealExtension.encoding d e) (FixedRealExtension.encoding d e) run ∧
      ∀a,FixedRealExtension.Valid d a→FixedRealExtension.value basis a≠0→
        FixedRealExtension.Valid d (run a) ∧
          FixedRealExtension.value basis (run a)=(FixedRealExtension.value basis a)⁻¹

def equalityProblem (basis:PresentationBasis d e K) : Problem :=
  typedProblem ((FixedRealExtension.encoding d e).prod (FixedRealExtension.encoding d e)) BitEncoding.bool
    (fun p=>FixedRealExtension.Valid d p.1 ∧ FixedRealExtension.Valid d p.2)
    (fun p b=>b=true ↔ FixedRealExtension.value basis p.1=FixedRealExtension.value basis p.2)

/-- All arithmetic/output clauses except the independently named inverse and
general prescribed-subfield conversion. Nothing computes the coloring counts. -/
structure EstablishedClauses (basis:PresentationBasis d e K) : Prop where
  addition : (FixedRealExtension.additionProblem basis).InFP
  multiplication : (FixedRealExtension.multiplicationProblem basis).InFP
  equality : (equalityProblem basis).InFP
  products : ∀t:ℕ,∀A:Fin t→K,(ProductProblem basis A).InFP
  nonsingularSystems : (FixedRealExtension.linearSystemProblem basis).InFP
  partitionOutputSize : PartitionOutputBound basis

structure ArithmeticClauses (basis:PresentationBasis d e K) : Prop extends EstablishedClauses basis where
  inversion : Inversion basis

/-- Finite extensions inherit a genuine fixed RF basis by the scalar tower.
Only the new fixed degree changes; no finite Q-basis is postulated. -/
def extensionBasis (basis:PresentationBasis d e K) (E:Type) [Field E] [Algebra K E]
    [Algebra (RationalFunction d) E] [IsScalarTower (RationalFunction d) K E] [FiniteDimensional K E] :
    PresentationBasis d (e*Module.finrank K E) E :=
  (basis.smulTower (Module.finBasis K E)).reindex finProdFinEquiv

/-- The input promise states known membership in the specified fixed subfield.
Every valid representative is accepted; membership is never decided. -/
def descentProblem {c f:ℕ} {F:Type} [Field F] [Algebra (RationalFunction c) F]
    (source:PresentationBasis d e K) (target:PresentationBasis c f F) (embed:F→+*K) : Problem :=
  typedProblem (FixedRealExtension.encoding d e) (FixedRealExtension.encoding c f)
    (fun a=>FixedRealExtension.Valid d a ∧ ∃z:F,FixedRealExtension.value source a=embed z)
    (fun a b=>FixedRealExtension.Valid c b ∧ embed (FixedRealExtension.value target b)=
      FixedRealExtension.value source a)

def PrescribedSubfieldDescent (basis:PresentationBasis d e K) : Prop :=
  ∀(c f:ℕ) (F:Type) [Field F] [Algebra (RationalFunction c) F],
    ∀target:PresentationBasis c f F,∀embed:F→+*K,(descentProblem basis target embed).InFP

def integerProblem (basis:PresentationBasis d e K) : Problem :=
  typedProblem (FixedRealExtension.encoding d e) BitEncoding.int
    (fun a=>FixedRealExtension.Valid d a ∧ ∃z:ℤ,FixedRealExtension.value basis a=(z:K))
    (fun a z=>FixedRealExtension.value basis a=(z:K))

def CompleteFieldClauses (basis:PresentationBasis d e K) : Prop :=
  ArithmeticClauses basis ∧ PrescribedSubfieldDescent basis ∧ (integerProblem basis).InFP

def FiniteExtensionClauses (basis:PresentationBasis d e K) : Prop :=
  ∀(E:Type) [Field E] [Algebra K E] [Algebra (RationalFunction d) E]
    [IsScalarTower (RationalFunction d) K E] [FiniteDimensional K E],
    CompleteFieldClauses (extensionBasis basis E)

/-- Full numbered endpoint: the original prescribed presentation, every fixed
finite algebraic extension, general specified subfields, and ordinary integers. -/
def LemmaA1Statement (basis:PresentationBasis d e K) : Prop :=
  CompleteFieldClauses basis ∧ FiniteExtensionClauses basis

end PlanarHom.FixedRealLemmaA1
