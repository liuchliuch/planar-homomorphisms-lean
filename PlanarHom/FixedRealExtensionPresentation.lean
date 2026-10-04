import PlanarHom.FixedRealExtensionMachines
import PlanarHom.FixedRealExtensionCompleteness

/-! Prescribed-field represented addition and multiplication for every fixed
finite extension of Q(X). The shared denominator table is constructed from the
fixed basis, with no finite Q-basis assumed for the extension field. -/
noncomputable section
namespace PlanarHom.FixedRealExtension
open DensePolynomial Complexity RepresentedBit
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

def normalizer (n e:ℕ) : BitEncoding.Normalizer (encoding n e) :=
  BitEncoding.prodNormalizer (BitEncoding.vectorNormalizer (DensePolynomial.normalizer n) e)
    (DensePolynomial.normalizer n)

def presentation (basis:Module.Basis (Fin e) (RationalFunction n) K) : Presentation K where
  Code:=Code n e
  encoding:=encoding n e
  valid:=Valid n
  value:=value basis
  complete:=value_complete basis
  normalizer:=normalizer n e

def additionProblem (basis:Module.Basis (Fin e) (RationalFunction n) K) : Problem :=
  (presentation basis).problem ((encoding n e).prod (encoding n e))
    (fun p=>Valid n p.1 ∧ Valid n p.2) (fun p=>value basis p.1+value basis p.2)

def multiplicationProblem (basis:Module.Basis (Fin e) (RationalFunction n) K) : Problem :=
  (presentation basis).problem ((encoding n e).prod (encoding n e))
    (fun p=>Valid n p.1 ∧ Valid n p.2) (fun p=>value basis p.1*value basis p.2)

theorem addition_inFP (basis:Module.Basis (Fin e) (RationalFunction n) K) :
    (additionProblem basis).InFP :=
  (presentation basis).problem_inFP _ (BitEncoding.prodNormalizer (normalizer n e) (normalizer n e)) _ _
    (fun p=>add n p.1 p.2) (fp_add n e)
    (fun p hp=>add_valid p.1 p.2 hp.1 hp.2) (fun p hp=>value_add basis p.1 p.2 hp.1 hp.2)

theorem multiplication_inFP (basis:Module.Basis (Fin e) (RationalFunction n) K) :
    (multiplicationProblem basis).InFP :=
  (presentation basis).problem_inFP _ (BitEncoding.prodNormalizer (normalizer n e) (normalizer n e)) _ _
    (fun p=>mul (multiplicationTable basis) p.1 p.2) (fp_mul n e (multiplicationTable basis))
    (fun p hp=>mul_valid _ p.1 p.2 hp.1 hp.2)
    (fun p _=>value_mul _ basis (multiplicationTable_realizes basis) p.1 p.2)

end PlanarHom.FixedRealExtension
