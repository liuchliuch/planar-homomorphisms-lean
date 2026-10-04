import PlanarHom.CoefficientListAlgebra
import PlanarHom.MaterializedPolynomialEvaluationMachines
import PlanarHom.ListDropMachines

/-! Actual synthetic division of runtime coefficient lists. Each quotient
coefficient is an evaluation of a strict suffix, so all intermediate words are
paid for by genuine suffix/evaluation/map machines, without a height premise. -/
noncomputable section
namespace PlanarHom.SyntheticDivisionMachines
open Complexity PairProjectionMachines

/-- Apply an actual FP program to every strict suffix, retaining one shared
context. This interface also accepts runtime radical-algebra evaluators. -/
theorem fp_strictSuffixMap {A B C : Type} (ea : BitEncoding A) (eb : BitEncoding B)
    (ec : BitEncoding C) (d : A) (f : C × List A → B)
    (hf : FP (ec.prod ea.list) eb f) :
    FP (ec.prod ea.list) eb.list (fun p : C × List A =>
      p.2.zipIdx.map (fun q => f (p.1,p.2.drop (q.2+1)))) := by
  let ei := ea.prod BitEncoding.nat
  let ectx := ec.prod ea.list
  have hctx := fp_fst ectx ei
  have hi := (fp_snd ectx ei).comp (fp_snd ea BitEncoding.nat)
  have hsucc := (hi.pair (fp_const (ectx.prod ei) BitEncoding.nat 1)).comp
    BinaryArithmetic.fp_addition
  have hxs := hctx.comp (fp_snd ec ea.list)
  have hc := hctx.comp (fp_fst ec ea.list)
  have hd := (hsucc.pair hxs).comp (ListDropMachines.fp_drop ea d)
  have hbody := (hc.pair hd).comp hf
  have hmap := ListContextMachines.fp_mapWithContext ectx ei eb _ hbody
  have hix := (fp_snd ec ea.list).comp (ListIndexMachines.fp_zipIdx ea)
  exact ((fp_id ectx).pair hix).comp hmap

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- Total coefficient evaluation under the ring-generic semantics. -/
theorem fp_evaluate : FP
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis)
    (fun p : K × List K => CoefficientListAlgebra.evaluate p.1 p.2) :=
  MaterializedPolynomialEvaluationMachines.fp_evaluate basis

/-- Exact ascending coefficients of division by X−b, retaining a trailing zero. -/
theorem fp_quotientCoefficients : FP
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis).list
    (fun p : K × List K => CoefficientListAlgebra.quotientCoefficients p.1 p.2) :=
  fp_strictSuffixMap _ _ _ (0 : K) _ (fp_evaluate basis)

end PlanarHom.SyntheticDivisionMachines
