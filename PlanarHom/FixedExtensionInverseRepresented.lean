import PlanarHom.FixedExtensionInverse

/-! NEW reconstruction: inversion and division have actual represented-bit
machines in the prescribed fixed-extension presentation. Zero inverse is zero,
and every successful, valid noncanonical input representation is accepted. -/
noncomputable section
namespace PlanarHom.FixedRealExtension
open DensePolynomial Complexity RepresentedBit PairProjectionMachines
variable {n e : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

def oneCode : Code n e := Classical.choose (value_complete basis 1)
theorem oneCode_valid : Valid n (oneCode basis) := (Classical.choose_spec (value_complete basis 1)).1
theorem oneCode_value : value basis (oneCode basis) = 1 := (Classical.choose_spec (value_complete basis 1)).2

def inversionProblem : Problem :=
  (presentation basis).problem (encoding n e) (Valid n) (fun a => (value basis a)⁻¹)

theorem inversion_inFP : (inversionProblem basis).InFP :=
  (presentation basis).problem_inFP _ (normalizer n e) _ _
    (inverse (multiplicationTable basis) (oneCode basis))
    (fp_inverse _ _)
    (fun a ha => inverse_valid basis _ (multiplicationTable_realizes basis) _ a (oneCode_valid basis) ha)
    (fun a ha => inverse_value basis _ (multiplicationTable_realizes basis) _ a
      (oneCode_valid basis) (oneCode_value basis) ha)

def divide (T : MultiplicationTable n e) (one : Code n e) (a b : Code n e) : Code n e :=
  mul T a (inverse T one b)

theorem fp_divide (T : MultiplicationTable n e) (one : Code n e) :
    FP ((encoding n e).prod (encoding n e)) (encoding n e) (fun p => divide T one p.1 p.2) :=
  ((fp_fst (encoding n e) (encoding n e)).pair
    ((fp_snd (encoding n e) (encoding n e)).comp (fp_inverse T one))).comp (fp_mul n e T)

theorem divide_valid (T : MultiplicationTable n e) (hT : T.Realizes basis)
    (one a b : Code n e) (h1 : Valid n one) (ha : Valid n a) (hb : Valid n b) :
    Valid n (divide T one a b) :=
  mul_valid T a _ ha (inverse_valid basis T hT one b h1 hb)

theorem divide_value (T : MultiplicationTable n e) (hT : T.Realizes basis)
    (one a b : Code n e) (h1 : Valid n one) (hv1 : value basis one = 1)
    (hb : Valid n b) : value basis (divide T one a b) = value basis a / value basis b := by
  rw [divide, value_mul T basis hT, inverse_value basis T hT one b h1 hv1 hb, div_eq_mul_inv]

def divisionProblem : Problem :=
  (presentation basis).problem ((encoding n e).prod (encoding n e))
    (fun p => Valid n p.1 ∧ Valid n p.2) (fun p => value basis p.1 / value basis p.2)

theorem division_inFP : (divisionProblem basis).InFP :=
  (presentation basis).problem_inFP _ (BitEncoding.prodNormalizer (normalizer n e) (normalizer n e)) _ _
    (fun p => divide (multiplicationTable basis) (oneCode basis) p.1 p.2)
    (fp_divide _ _)
    (fun p hp => divide_valid basis _ (multiplicationTable_realizes basis) _ p.1 p.2
      (oneCode_valid basis) hp.1 hp.2)
    (fun p hp => divide_value basis _ (multiplicationTable_realizes basis) _ p.1 p.2
      (oneCode_valid basis) (oneCode_value basis) hp.2)

end PlanarHom.FixedRealExtension
