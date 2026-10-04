import PlanarHom.FixedRealExtensionPresentation
import PlanarHom.DensePolynomialEvaluationMachines

/-! Dynamic rational coefficients act on fixed-extension representatives by
scaling every polynomial numerator and preserving the shared denominator. -/
noncomputable section
namespace PlanarHom.FixedRealExtension
open DensePolynomial Complexity PairProjectionMachines
variable {n e:ℕ}

def rationalScale (n:ℕ) (q:ℚ) (a:Code n e) : Code n e :=
  (fun k=>DensePolynomial.scalar n q (a.1 k),a.2)

theorem rationalScale_valid (q:ℚ) (a:Code n e) (h:Valid n a) : Valid n (rationalScale n q a) := h

theorem rationalScale_coordinates (q:ℚ) (a:Code n e) :
    coordinates n (rationalScale n q a)=
      algebraMap (Poly n) (RationalFunction n) (qHom n q) • coordinates n a := by
  funext k
  simp only [coordinates,rationalScale,fractionValue,interpret_scalar,map_mul,Pi.smul_apply,smul_eq_mul]
  rw [mul_div_assoc]

theorem rationalScale_value {K:Type} [Field K] [Algebra (RationalFunction n) K]
    (basis:Module.Basis (Fin e) (RationalFunction n) K) (q:ℚ) (a:Code n e) :
    value basis (rationalScale n q a)=(q:K)*value basis a := by
  rw [value,rationalScale_coordinates,map_smul,Algebra.smul_def]
  have hq:algebraMap (RationalFunction n) K (algebraMap (Poly n) (RationalFunction n) (qHom n q))=(q:K) :=
    eq_ratCast ((algebraMap (RationalFunction n) K).comp ((algebraMap (Poly n) (RationalFunction n)).comp (qHom n))) q
  rw [hq]
  rfl

theorem fp_rationalScale (n e:ℕ) :
    FP (rationalCode.prod (encoding n e)) (encoding n e) (fun p=>rationalScale n p.1 p.2) := by
  let ep:=DensePolynomial.encoding n
  let ec:=encoding n e
  have hq:=fp_fst rationalCode ec
  have ha:=fp_snd rationalCode ec
  have hn:FP (rationalCode.prod ec) (ep.vector e)
      (fun p k=>DensePolynomial.scalar n p.1 (p.2.1 k)) := by
    apply FixedVectorMachines.fp_assemble
    intro k
    exact (hq.pair ((ha.comp (fp_fst (ep.vector e) ep)).comp (FixedVectorMachines.fp_coordinate ep e k))).comp
      (DensePolynomial.fp_scalar n)
  exact hn.pair (ha.comp (fp_snd (ep.vector e) ep))

end PlanarHom.FixedRealExtension
