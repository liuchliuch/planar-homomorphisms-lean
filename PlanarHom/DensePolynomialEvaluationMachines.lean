import PlanarHom.DensePolynomialEvaluation

/-! NEW actual TM2 bit algorithms for scalar multiplication and rational grid
point evaluation of a fixed-variable dense polynomial. Dynamic rational powers
use materialized products with proved complete intermediate bit bounds. -/
noncomputable section
namespace PlanarHom.DensePolynomial
open Complexity PairProjectionMachines
abbrev rationalCode:=encoding 0

 theorem fp_rationalPower : FP (BitEncoding.unaryNat.prod rationalCode) rationalCode
    (fun p:ℕ×ℚ=>p.2^p.1) := by
  exact ((RuntimePolynomialEvaluationMachines.fp_replicate rationalCode).comp
    (MaterializedFieldListMachines.fp_product rationalBasis)).congr (fun p=>by simp)

 theorem fp_univariateEvaluate : FP (rationalCode.prod rationalCode.list) rationalCode
    (fun p=>CoefficientListAlgebra.evaluate p.1 p.2) := by
  let ec:=BitEncoding.nat
  have hm:=(fp_snd ec (rationalCode.prod rationalCode)).comp
    (FixedFieldArithmetic.fp_multiplication rationalBasis)
  have hp:=(fp_snd ec (BitEncoding.unaryNat.prod rationalCode)).comp fp_rationalPower
  have hs:=(fp_snd ec rationalCode.list).comp (MaterializedFieldListMachines.fp_sum rationalBasis)
  have he:=RuntimePolynomialEvaluationMachines.fp_evaluate rationalCode ec
    (fun (_:ℕ) (x y:ℚ)=>x*y) (fun (_:ℕ) n (x:ℚ)=>x^n) (fun (_:ℕ) (xs:List ℚ)=>xs.sum) hm hp hs
  exact (((fp_const (rationalCode.prod rationalCode.list) ec 0).pair
    (fp_id (rationalCode.prod rationalCode.list))).comp he).congr (fun _=>rfl)

 theorem fp_scalar (n:ℕ) : FP (rationalCode.prod (encoding n)) (encoding n)
    (fun p=>scalar n p.1 p.2) := by
  induction n with
  | zero=>exact FixedFieldArithmetic.fp_multiplication rationalBasis
  | succ n ih=>exact ListContextMachines.fp_mapWithContext rationalCode (encoding n) (encoding n) _ ih

 theorem fp_evaluate (n:ℕ) : FP ((encoding n).prod rationalCode.list) rationalCode
    (fun p=>evaluate n p.1 p.2) := by
  induction n with
  | zero=>exact fp_fst rationalCode rationalCode.list
  | succ n ih=>
    let ep:=(encoding n).list
    have hc:=fp_fst ep rationalCode.list
    have hx:=fp_snd ep rationalCode.list
    have hb:=hx.comp (ListDecompositionMachines.fp_headD rationalCode 0)
    have ht:=hx.comp (ListDecompositionMachines.fp_tail rationalCode 0)
    have hbody:=((fp_snd rationalCode.list (encoding n)).pair
      (fp_fst rationalCode.list (encoding n))).comp ih
    have hv:=((ht.pair hc).comp
      (ListContextMachines.fp_mapWithContext rationalCode.list (encoding n) rationalCode _ hbody))
    exact (hb.pair hv).comp fp_univariateEvaluate

end PlanarHom.DensePolynomial
