import PlanarHom.RuntimePolynomialEvaluationMachines
import PlanarHom.BooleanFieldTowerProjectorMachines

/-! Actual runtime polynomial evaluation and synthetic coefficient division in
the possibly non-domain radical algebra. -/
noncomputable section
namespace PlanarHom.BooleanFieldTowerPolynomialMachines
open Complexity PairProjectionMachines BooleanFieldTower BooleanFieldTowerMachines
open BooleanFieldTowerAlgebra BooleanFieldTowerConvolutionMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

theorem fold_replicate_power (D : ℕ → K) (n : ℕ) (a : Tower K n) (k : ℕ) :
    (List.replicate k a).foldl (mul D n) (embed n 1) = power D n a k := by
  have h := BooleanFieldTowerProductMachines.fold_mul_eq D n
    (List.replicate k (ofTower D n a)) (1 : Carrier D n)
  rw [List.prod_replicate, one_mul] at h
  simpa only [one_eq, pow_eq, ofTower] using h

theorem fp_power (n : ℕ) : FP
    ((numberFieldEncoding basis).list.prod (BitEncoding.unaryNat.prod (encoding basis n)))
    (encoding basis n) (fun p : List K × (ℕ × Tower K n) => power (radicands p.1) n p.2.2 p.2.1) := by
  apply (RuntimePolynomialEvaluationMachines.fp_power (encoding basis n) (numberFieldEncoding basis).list
    (embed n 1) (fun ds a xs => xs.foldl (mul (radicands ds) n) a)
    (BooleanFieldTowerProductMachines.fp_product basis n)).congr
  intro p
  exact fold_replicate_power (radicands p.1) n p.2.2 p.2.1

def evaluate (n : ℕ) (p : List K × (Tower K n × List (Tower K n))) : Tower K n :=
  RuntimePolynomialEvaluationMachines.evaluate (fun ds => mul (radicands ds) n)
    (fun ds k a => power (radicands ds) n a k) (fun _ => BooleanFieldTowerSumMachines.sum n) p

theorem fp_evaluate (n : ℕ) : FP
    ((numberFieldEncoding basis).list.prod ((encoding basis n).prod (encoding basis n).list))
    (encoding basis n) (evaluate n) :=
  RuntimePolynomialEvaluationMachines.fp_evaluate (encoding basis n) (numberFieldEncoding basis).list
    (fun ds => mul (radicands ds) n) (fun ds k a => power (radicands ds) n a k)
    (fun _ => BooleanFieldTowerSumMachines.sum n)
    (BooleanFieldTowerConvolutionMachines.fp_mul basis n) (fp_power basis n)
    ((fp_snd _ _).comp (BooleanFieldTowerSumMachines.fp_sum basis n))

theorem evaluate_eq (n : ℕ) (ds : List K) (b : Carrier (radicands ds) n)
    (cs : List (Carrier (radicands ds) n)) :
    evaluate n (ds,(b,cs)) = CoefficientListAlgebra.evaluate b cs := by
  unfold evaluate RuntimePolynomialEvaluationMachines.evaluate CoefficientListAlgebra.evaluate
  simp only [sum_eq, mul_eq, pow_eq]
  rfl

def quotientCoefficients (n : ℕ) (p : List K × (Tower K n × List (Tower K n))) : List (Tower K n) :=
  p.2.2.zipIdx.map (fun q => evaluate n (p.1,(p.2.1,p.2.2.drop (q.2+1))))

theorem fp_quotientCoefficients (n : ℕ) : FP
    ((numberFieldEncoding basis).list.prod ((encoding basis n).prod (encoding basis n).list))
    (encoding basis n).list (quotientCoefficients n) := by
  let e := encoding basis n
  let ed := (numberFieldEncoding basis).list
  let ec := ed.prod e
  have hc := fp_fst ec e.list
  have hs := fp_snd ec e.list
  have hd := hc.comp (fp_fst ed e)
  have hb := hc.comp (fp_snd ed e)
  have he := (hd.pair (hb.pair hs)).comp (fp_evaluate basis n)
  have hm := SyntheticDivisionMachines.fp_strictSuffixMap e e ec (zero n)
    (fun p => evaluate n (p.1.1,(p.1.2,p.2))) he
  have hd' := fp_fst ed (e.prod e.list)
  have ht := fp_snd ed (e.prod e.list)
  have hb' := ht.comp (fp_fst e e.list)
  have hcs := ht.comp (fp_snd e e.list)
  exact ((hd'.pair hb').pair hcs).comp hm

theorem quotientCoefficients_eq (n : ℕ) (ds : List K) (b : Carrier (radicands ds) n)
    (cs : List (Carrier (radicands ds) n)) :
    quotientCoefficients n (ds,(b,cs)) = CoefficientListAlgebra.quotientCoefficients b cs := by
  simp only [quotientCoefficients, CoefficientListAlgebra.quotientCoefficients, evaluate_eq]
  rfl

theorem quotient_polynomial (n : ℕ) (ds : List K) (b : Carrier (radicands ds) n)
    (cs : List (Carrier (radicands ds) n)) :
    CoefficientListAlgebra.polynomial (R := Carrier (radicands ds) n)
      (quotientCoefficients n (ds,(b,cs))) =
      CoefficientListAlgebra.polynomial cs /ₘ (Polynomial.X-Polynomial.C b) := by
  rw [quotientCoefficients_eq, CoefficientListAlgebra.quotient_polynomial]

end PlanarHom.BooleanFieldTowerPolynomialMachines
