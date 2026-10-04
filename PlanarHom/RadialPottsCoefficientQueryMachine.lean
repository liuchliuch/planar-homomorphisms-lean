import PlanarHom.RadialPottsNumericQuery
import PlanarHom.PottsCoefficientPrograms

/-! Actual encoded pair of a binary coefficient index and the ordinary radial
graph query. The graph compiler and index arithmetic both run in polynomial time. -/
namespace PlanarHom.RadialPotts.Numeric
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

 def coefficientQuery (p : Input) : ℕ×MixedCode := (coefficientDegree p,query p)

 theorem fp_coefficientDegree : FP inputEncoding BitEncoding.nat coefficientDegree := by
  have hm := fp_fst BitEncoding.unaryNat (BitEncoding.unaryNat.prod BitEncoding.nat.list)
  have hk := (fp_snd BitEncoding.unaryNat (BitEncoding.unaryNat.prod BitEncoding.nat.list)).comp
    (fp_fst BitEncoding.unaryNat BitEncoding.nat.list)
  have h1 := fp_const inputEncoding BitEncoding.unaryNat 1
  have h2 := fp_const inputEncoding BitEncoding.unaryNat 2
  have hk1 := (hk.pair h1).comp UnaryPolynomialMachines.fp_add
  have h2k := (h2.pair hk).comp UnaryPolynomialMachines.fp_mul
  have hlong := (((h2k.pair hk1).comp UnaryPolynomialMachines.fp_mul).pair hm).comp UnaryPolynomialMachines.fp_mul
  have hshort := (((h2k.pair hk).comp UnaryPolynomialMachines.fp_mul).pair hm).comp UnaryPolynomialMachines.fp_mul
  have hn := (fp_pathPrivateCount.pair h1).comp UnaryPolynomialMachines.fp_add
  have hd := (((hn.pair hlong).comp UnaryPolynomialMachines.fp_mul).pair hshort).comp UnaryPolynomialMachines.fp_add
  exact (hd.comp UnaryNatConversionMachine.fp_conversion).congr
    (fun _ => by simp only [coefficientDegree,pow_two,Function.comp_apply,id_eq]; ring)

 theorem fp_coefficientQuery : FP inputEncoding PottsCoefficientPrograms.inputEncoding coefficientQuery :=
  fp_coefficientDegree.pair fp_query
end PlanarHom.RadialPotts.Numeric
