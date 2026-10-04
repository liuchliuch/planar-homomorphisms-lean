import PlanarHom.FixedRealExtensionCode

/-! Actual polynomial-bit addition/negation/multiplication for shared-denominator
extension coordinates. Both transcendence count and algebraic degree are fixed;
all polynomial degrees and coefficient lengths remain input-dependent. -/
noncomputable section
namespace PlanarHom.FixedRealExtension
open Complexity PairProjectionMachines DensePolynomial

variable (n e:ℕ)

private theorem fp_numerator (i:Fin e) :
    FP (encoding n e) (DensePolynomial.encoding n) (fun a:Code n e=>a.1 i) :=
  (fp_fst ((DensePolynomial.encoding n).vector e) (DensePolynomial.encoding n)).comp
    (FixedVectorMachines.fp_coordinate (DensePolynomial.encoding n) e i)

private theorem fp_denominator : FP (encoding n e) (DensePolynomial.encoding n) (fun a:Code n e=>a.2) :=
  fp_snd ((DensePolynomial.encoding n).vector e) (DensePolynomial.encoding n)

theorem fp_add : FP ((encoding n e).prod (encoding n e)) (encoding n e)
    (fun p=>add n p.1 p.2) := by
  let ec:=encoding n e
  let ep:=DensePolynomial.encoding n
  have ha:=fp_fst ec ec
  have hb:=fp_snd ec ec
  have had:=ha.comp (fp_denominator n e)
  have hbd:=hb.comp (fp_denominator n e)
  have hn:FP (ec.prod ec) (ep.vector e) (fun p i=>
      DensePolynomial.add n (DensePolynomial.mul n (p.1.1 i) p.2.2)
        (DensePolynomial.mul n (p.2.1 i) p.1.2)) := by
    apply FixedVectorMachines.fp_assemble
    intro i
    have hl:=((ha.comp (fp_numerator n e i)).pair hbd).comp (DensePolynomial.fp_mul n)
    have hr:=((hb.comp (fp_numerator n e i)).pair had).comp (DensePolynomial.fp_mul n)
    exact (hl.pair hr).comp (DensePolynomial.fp_add n)
  exact hn.pair ((had.pair hbd).comp (DensePolynomial.fp_mul n))

theorem fp_neg : FP (encoding n e) (encoding n e) (neg n) := by
  have hn:FP (encoding n e) ((DensePolynomial.encoding n).vector e)
      (fun a i=>DensePolynomial.neg n (a.1 i)) := by
    apply FixedVectorMachines.fp_assemble
    intro i
    exact (fp_numerator n e i).comp (DensePolynomial.fp_neg n)
  exact hn.pair (fp_denominator n e)

theorem fp_mul (T:MultiplicationTable n e) :
    FP ((encoding n e).prod (encoding n e)) (encoding n e) (fun p=>mul T p.1 p.2) := by
  let ec:=encoding n e
  let ep:=DensePolynomial.encoding n
  have ha:=fp_fst ec ec
  have hb:=fp_snd ec ec
  have hn:FP (ec.prod ec) (ep.vector e) (fun p k=>
      fixedSum n e (fun i=>fixedSum n e (fun j=>
        DensePolynomial.mul n (DensePolynomial.mul n (p.1.1 i) (p.2.1 j)) (T.numerator i j k)))) := by
    apply FixedVectorMachines.fp_assemble
    intro k
    apply fp_fixedSum
    intro i
    apply fp_fixedSum
    intro j
    have hl:=((ha.comp (fp_numerator n e i)).pair (hb.comp (fp_numerator n e j))).comp (DensePolynomial.fp_mul n)
    exact (hl.pair (fp_const (ec.prod ec) ep (T.numerator i j k))).comp (DensePolynomial.fp_mul n)
  have hd:=((ha.comp (fp_denominator n e)).pair (hb.comp (fp_denominator n e))).comp (DensePolynomial.fp_mul n)
  exact hn.pair ((hd.pair (fp_const (ec.prod ec) ep T.denominator)).comp (DensePolynomial.fp_mul n))

end PlanarHom.FixedRealExtension
