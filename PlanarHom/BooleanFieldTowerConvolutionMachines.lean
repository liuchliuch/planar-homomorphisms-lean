import PlanarHom.CoefficientConvolutionMachines
import PlanarHom.BooleanFieldTowerSumMachines
import PlanarHom.BooleanFieldTowerAlgebra
import PlanarHom.DependentMonomialMachines

/-! Actual polynomial convolution in the possibly non-domain radical algebra.
The radicand list is literal runtime input; only base-field arithmetic is used. -/
noncomputable section
namespace PlanarHom.BooleanFieldTowerConvolutionMachines
open Complexity PairProjectionMachines BooleanFieldTower BooleanFieldTowerMachines
open BooleanFieldTowerAlgebra
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def radicands (ds : List K) (i : ℕ) : K := ds[i]?.getD 0

theorem fp_mul (n : ℕ) : FP
    ((numberFieldEncoding basis).list.prod ((encoding basis n).prod (encoding basis n)))
    (encoding basis n)
    (fun p : List K × (Tower K n × Tower K n) => mul (radicands p.1) n p.2.1 p.2.2) := by
  let e := encoding basis n
  let ed := (numberFieldEncoding basis).list
  let ei := ed.prod (e.prod e)
  have hd := fp_fst ed (e.prod e)
  have hs := fp_snd ed (e.prod e)
  exact BooleanFieldTowerMachines.fp_mul basis ei (fun p => radicands p.1)
    (fun i => hd.comp (DependentMonomialMachines.fp_getD (numberFieldEncoding basis) 0 i)) n _ _
    (hs.comp (fp_fst e e)) (hs.comp (fp_snd e e))

def convolution (n : ℕ) (p : List K × (List (Tower K n) × List (Tower K n))) :
    List (Tower K n) :=
  CoefficientConvolutionMachines.convolution (zero n) (fun ds => mul (radicands ds) n)
    (fun _ => BooleanFieldTowerSumMachines.sum n) p

/-- Runtime polynomial multiplication with no field assumption on the tower
and no user-supplied intermediate-size bound. -/
theorem fp_convolution (n : ℕ) : FP
    ((numberFieldEncoding basis).list.prod ((encoding basis n).list.prod (encoding basis n).list))
    (encoding basis n).list (convolution n) :=
  CoefficientConvolutionMachines.fp_convolution (encoding basis n) (numberFieldEncoding basis).list
    (zero n) (fun ds => mul (radicands ds) n) (fun _ => BooleanFieldTowerSumMachines.sum n)
    (fp_mul basis n) ((fp_snd _ _).comp (BooleanFieldTowerSumMachines.fp_sum basis n))

omit [Algebra ℚ K] in
theorem sum_eq (D : ℕ → K) (n : ℕ) (xs : List (Carrier D n)) :
    xs.sum = (BooleanFieldTowerSumMachines.sum n xs : Tower K n) := by
  induction xs with
  | nil => exact zero_eq D n
  | cons x xs ih =>
    rw [List.sum_cons, add_eq, ih]
    rfl

omit [Algebra ℚ K] in
theorem convolution_eq (n : ℕ) (p : List K × (List (Tower K n) × List (Tower K n))) :
    convolution n p = CoefficientListAlgebra.convolution
      (R := Carrier (radicands p.1) n) p.2.1 p.2.2 := by
  unfold convolution CoefficientConvolutionMachines.convolution CoefficientListAlgebra.convolution
  apply List.map_congr_left
  intro k _
  simp only [CoefficientConvolutionMachines.coefficient, CoefficientListAlgebra.convolutionCoefficient,
    CoefficientConvolutionMachines.term, sum_eq, mul_eq, zero_eq]
  rfl

omit [Algebra ℚ K] in
/-- Coefficient-list semantics for the actual runtime-radicand compiler. -/
theorem convolution_polynomial (n : ℕ) (p : List K × (List (Tower K n) × List (Tower K n))) :
    CoefficientListAlgebra.polynomial (R := Carrier (radicands p.1) n) (convolution n p) =
      CoefficientListAlgebra.polynomial (R := Carrier (radicands p.1) n) p.2.1 *
        CoefficientListAlgebra.polynomial (R := Carrier (radicands p.1) n) p.2.2 := by
  rw [convolution_eq]
  exact CoefficientListAlgebra.convolution_polynomial _ _

end PlanarHom.BooleanFieldTowerConvolutionMachines
