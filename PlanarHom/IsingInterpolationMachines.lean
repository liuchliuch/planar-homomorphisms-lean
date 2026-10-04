import PlanarHom.IsingRationalSampleSemantics
import PlanarHom.FKTIsingUniformRational
import PlanarHom.DensePolynomialEvaluationMachines

/-! NEW actual polynomial-time generation of all Ising coefficients. The
sample call consumes graph and rational parameter jointly; fixed-parameter
computability is not used to infer uniform computation. -/
noncomputable section
namespace PlanarHom.IsingRationalInterpolation
open Complexity PairProjectionMachines
abbrev rationalCode:=DensePolynomial.rationalCode
abbrev tableCode:=(rationalCode.prod rationalCode).list

theorem fp_node : FP BitEncoding.nat rationalCode node := by
  have hn:=FixedFieldPolynomialMachines.fp_natCast DensePolynomial.rationalBasis
  exact ((hn.pair (fp_const BitEncoding.nat rationalCode (1:ℚ))).comp
    (FixedFieldArithmetic.fp_addition DensePolynomial.rationalBasis)).congr (fun _=>rfl)

theorem fp_indices : FP MixedCode.encoding BitEncoding.nat.list
    (fun g:MixedCode=>List.range (g.edges.length+1)) :=
  (MixedCode.fp_edges.comp (ListUnaryLengthMachine.fp_length
    (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)))).comp
      (UnaryArithmeticMachines.fp_succ.comp UnaryArithmeticMachines.fp_range)

theorem fp_planarSample : FP (MixedCode.encoding.prod BitEncoding.nat)
    (rationalCode.prod rationalCode) (fun p=>(node p.2,FKTIsingMachines.value (node p.2) p.1)) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have hn:=(fp_snd MixedCode.encoding BitEncoding.nat).comp fp_node
  exact hn.pair ((hg.pair hn).comp (FKTIsingUniform.fp_value DensePolynomial.rationalBasis))

theorem fp_planarTable : FP MixedCode.encoding tableCode planarTable :=
  ((fp_id MixedCode.encoding).pair fp_indices).comp
    (ListContextMachines.fp_mapWithContext MixedCode.encoding BitEncoding.nat
      (rationalCode.prod rationalCode) _ fp_planarSample)

theorem fp_coefficients : FP (BitEncoding.unaryNat.prod tableCode) rationalCode.list
    (fun p=>coefficients p.1 p.2) := by
  have hi:=(fp_fst BitEncoding.unaryNat tableCode).comp
    (UnaryArithmeticMachines.fp_succ.comp UnaryArithmeticMachines.fp_range)
  have ht:=fp_snd BitEncoding.unaryNat tableCode
  have hk:=(fp_snd tableCode BitEncoding.nat).pair (fp_fst tableCode BitEncoding.nat)
  have hr:=hk.comp (MaterializedPolynomialCoefficientMachines.fp_recover DensePolynomial.rationalBasis)
  exact (ht.pair hi).comp
    (ListContextMachines.fp_mapWithContext tableCode BitEncoding.nat rationalCode _ hr)

theorem fp_planarCoefficients : FP MixedCode.encoding rationalCode.list planarCoefficients := by
  have hd:=MixedCode.fp_edges.comp (ListUnaryLengthMachine.fp_length
    (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)))
  exact (hd.pair fp_planarTable).comp fp_coefficients

end PlanarHom.IsingRationalInterpolation
