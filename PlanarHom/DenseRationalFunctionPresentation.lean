import PlanarHom.DensePolynomialArithmeticMachines
import PlanarHom.DenseRationalFunctionCompleteness
import PlanarHom.RepresentedFieldEncoding

/-! Genuine represented rational-function arithmetic on arbitrary successful
raw encodings. Every mathematically valid numerator/denominator representative
is admitted; outputs are interpreted in the prescribed fraction field. -/
noncomputable section
namespace PlanarHom.DensePolynomial
open Complexity RepresentedBit

def normalizer : (n:ℕ)→BitEncoding.Normalizer (encoding n)
  | 0 => BitEncoding.numberFieldNormalizer rationalBasis
  | n+1 => BitEncoding.listNormalizer (normalizer n)

def fractionNormalizer (n:ℕ) : BitEncoding.Normalizer (fractionEncoding n) :=
  BitEncoding.prodNormalizer (normalizer n) (normalizer n)

def rationalFunctionPresentation (n:ℕ) : Presentation (RationalFunction n) where
  Code:=FractionCode n
  encoding:=fractionEncoding n
  valid:=FractionValid n
  value:=fractionValue n
  complete:=fraction_complete n
  normalizer:=fractionNormalizer n

def binaryValid (n:ℕ) (p:FractionCode n×FractionCode n) : Prop :=
  FractionValid n p.1 ∧ FractionValid n p.2

def multiplicationProblem (n:ℕ) : Problem :=
  (rationalFunctionPresentation n).problem ((fractionEncoding n).prod (fractionEncoding n))
    (binaryValid n) (fun p=>fractionValue n p.1*fractionValue n p.2)

def additionProblem (n:ℕ) : Problem :=
  (rationalFunctionPresentation n).problem ((fractionEncoding n).prod (fractionEncoding n))
    (binaryValid n) (fun p=>fractionValue n p.1+fractionValue n p.2)

def negationProblem (n:ℕ) : Problem :=
  (rationalFunctionPresentation n).problem (fractionEncoding n)
    (FractionValid n) (fun p=> -fractionValue n p)

def inversionProblem (n:ℕ) : Problem :=
  (rationalFunctionPresentation n).problem (fractionEncoding n)
    (fun p=>FractionValid n p ∧ fractionValue n p≠0) (fun p=>(fractionValue n p)⁻¹)

def equalityProblem (n:ℕ) : Problem :=
  typedProblem ((fractionEncoding n).prod (fractionEncoding n)) BitEncoding.bool (binaryValid n)
    (fun p b=>b=true ↔ fractionValue n p.1=fractionValue n p.2)

theorem multiplication_inFP (n:ℕ) : (multiplicationProblem n).InFP :=
  (rationalFunctionPresentation n).problem_inFP _
    (BitEncoding.prodNormalizer (fractionNormalizer n) (fractionNormalizer n)) _ _
    (fun p=>fractionMul n p.1 p.2) (fp_fractionMul n)
    (fun p hp=>fractionMul_valid n p.1 p.2 hp.1 hp.2)
    (fun p _=>fractionValue_mul n p.1 p.2)

theorem addition_inFP (n:ℕ) : (additionProblem n).InFP :=
  (rationalFunctionPresentation n).problem_inFP _
    (BitEncoding.prodNormalizer (fractionNormalizer n) (fractionNormalizer n)) _ _
    (fun p=>fractionAdd n p.1 p.2) (fp_fractionAdd n)
    (fun p hp=>fractionAdd_valid n p.1 p.2 hp.1 hp.2)
    (fun p hp=>fractionValue_add n p.1 p.2 hp.1 hp.2)

theorem negation_inFP (n:ℕ) : (negationProblem n).InFP :=
  (rationalFunctionPresentation n).problem_inFP _ (fractionNormalizer n) _ _
    (fractionNeg n) (fp_fractionNeg n) (fractionNeg_valid n) (fun p _=>fractionValue_neg n p)

theorem inversion_inFP (n:ℕ) : (inversionProblem n).InFP :=
  (rationalFunctionPresentation n).problem_inFP _ (fractionNormalizer n) _ _
    (fractionInv n) (fp_fractionInv n) (fun p hp=>fractionInv_valid n p hp.2)
    (fun p _=>fractionValue_inv n p)

theorem equality_inFP (n:ℕ) : (equalityProblem n).InFP :=
  typedProblem_inFP _ BitEncoding.bool
    (BitEncoding.prodNormalizer (fractionNormalizer n) (fractionNormalizer n)) _ _
    (fun p=>fractionEq n p.1 p.2) (fp_fractionEq n)
    (fun p hp=>fractionEq_value_iff n p.1 p.2 hp.1 hp.2)

end PlanarHom.DensePolynomial
