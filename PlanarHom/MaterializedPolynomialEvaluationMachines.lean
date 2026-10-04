import PlanarHom.MaterializedPowerMachines
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.LinearFactorCoefficientMachines
import PlanarHom.ListIndexMachines
import PlanarHom.ListUnaryLengthMachine

/-! Exact evaluation of an arbitrary runtime coefficient list. The unary exponent
cap is physically computed from the list; all powers and sums are actual FP
programs with their already proved canonical-height bounds. -/
noncomputable section
namespace PlanarHom.MaterializedPolynomialEvaluationMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def evaluate (a : K) (cs : List K) : K :=
  (cs.zipIdx.map (fun p => p.1 * a ^ p.2)).sum

omit [Algebra ℚ K] in
theorem shifted_sum (a : K) (cs : List K) (j : ℕ) :
    ((cs.zipIdx j).map (fun p => p.1 * a ^ p.2)).sum =
      a ^ j * (LinearFactorCoefficientMachines.coefficientPolynomial cs).eval a := by
  induction cs generalizing j with
  | nil => simp [LinearFactorCoefficientMachines.coefficientPolynomial]
  | cons c cs ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, ih,
      LinearFactorCoefficientMachines.coefficientPolynomial, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, pow_succ]
    ring

omit [Algebra ℚ K] in
theorem evaluate_eq (a : K) (cs : List K) :
    evaluate a cs = (LinearFactorCoefficientMachines.coefficientPolynomial cs).eval a := by
  simpa [evaluate] using shifted_sum a cs 0

/-- Total term evaluation, with a literal unary cap guarding binary indices. -/
def cappedTerm (p : (ℕ × K) × (K × ℕ)) : K :=
  p.2.1 * p.1.2 ^ min p.1.1 p.2.2

theorem fp_cappedTerm : FP
    ((BitEncoding.unaryNat.prod (numberFieldEncoding basis)).prod
      ((numberFieldEncoding basis).prod BitEncoding.nat))
    (numberFieldEncoding basis) cappedTerm := by
  let e := numberFieldEncoding basis
  let ec := BitEncoding.unaryNat.prod e
  let ei := e.prod BitEncoding.nat
  have hc := fp_fst ec ei
  have ht := fp_snd ec ei
  have hn := hc.comp (fp_fst BitEncoding.unaryNat e)
  have ha := hc.comp (fp_snd BitEncoding.unaryNat e)
  have hv := ht.comp (fp_fst e BitEncoding.nat)
  have hi := ht.comp (fp_snd e BitEncoding.nat)
  have hp := (hn.pair (ha.pair hi)).comp (MaterializedPowerMachines.fp_boundedPower basis)
  exact (hv.pair hp).comp (FixedFieldArithmetic.fp_multiplication basis)

/-- Runtime coefficient count and values are ordinary materialized input. -/
theorem fp_evaluate : FP
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis) (fun p : K × List K => evaluate p.1 p.2) := by
  let e := numberFieldEncoding basis
  have ha := fp_fst e e.list
  have hcs := fp_snd e e.list
  have hn := hcs.comp (ListUnaryLengthMachine.fp_length e)
  have hi := hcs.comp (ListIndexMachines.fp_zipIdx e)
  have hm := ((hn.pair ha).pair hi).comp
    (ListContextMachines.fp_mapWithContext (BitEncoding.unaryNat.prod e)
      (e.prod BitEncoding.nat) e cappedTerm (fp_cappedTerm basis))
  apply (hm.comp (MaterializedFieldListMachines.fp_sum basis)).congr
  intro p
  change (p.2.zipIdx.map (fun x => cappedTerm ((p.2.length,p.1),x))).sum =
    (p.2.zipIdx.map (fun x => x.1 * p.1 ^ x.2)).sum
  congr 1
  apply List.map_congr_left
  intro x hx
  have hi : x.2 < p.2.length := by
    exact List.snd_lt_of_mem_zipIdx hx
  simp only [cappedTerm, min_eq_right (Nat.le_of_lt hi)]

end PlanarHom.MaterializedPolynomialEvaluationMachines
