import PlanarHom.SurfaceBooleanLinearCombination
import PlanarHom.SurfaceBooleanQuotient

/-! NEW complete encoded quotient preparation, coefficient extraction and
representative-chain synthesis, all from literal input row lists. -/
namespace PlanarHom.SurfaceBooleanRows
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
abbrev QuotientData := BasisRows×BasisRows
abbrev quotientDataCode := basisCode.prod basisCode
abbrev rowFamiliesCode := rowCode.list.prod rowCode.list

def prepareQuotient (faces cycles : List Row) : QuotientData :=
  (basis faces,quotientRows faces cycles)
def encodeQuotient (d : QuotientData) (r : Row) : Row := coefficients d.2 (reduce d.1 r)
def liftQuotient (d : QuotientData) (bits : Row) : Row := linearCombination d.2 bits

theorem fp_quotientRows : FP rowFamiliesCode basisCode (fun p => quotientRows p.1 p.2) := by
  have hbs := (fp_fst rowCode.list rowCode.list).comp fp_basis
  have hxs := fp_snd rowCode.list rowCode.list
  have hb := fp_fst basisCode rowCode
  have hr := fp_snd basisCode rowCode
  have hred := (hr.pair hb).comp fp_reduce
  have hm := (hbs.pair hxs).comp
    (ListContextMachines.fp_mapWithContext basisCode rowCode rowCode _ hred)
  exact hm.comp fp_basis

theorem fp_prepareQuotient : FP rowFamiliesCode quotientDataCode (fun p => prepareQuotient p.1 p.2) :=
  ((fp_fst rowCode.list rowCode.list).comp fp_basis).pair fp_quotientRows

theorem fp_encodeQuotient : FP (quotientDataCode.prod rowCode) rowCode (fun p => encodeQuotient p.1 p.2) := by
  have hd := fp_fst quotientDataCode rowCode
  have hf := hd.comp (fp_fst basisCode basisCode)
  have hq := hd.comp (fp_snd basisCode basisCode)
  have hr := fp_snd quotientDataCode rowCode
  exact (((hr.pair hf).comp fp_reduce).pair hq).comp fp_coefficients

theorem fp_liftQuotient : FP (quotientDataCode.prod rowCode) rowCode (fun p => liftQuotient p.1 p.2) := by
  have hq := (fp_fst quotientDataCode rowCode).comp (fp_snd basisCode basisCode)
  exact (hq.pair (fp_snd quotientDataCode rowCode)).comp fp_linearCombination

theorem encodeQuotient_value (faces cycles : List Row) (r : Row)
    (i : Fin (quotientRows faces cycles).length) :
    value (encodeQuotient (prepareQuotient faces cycles) r) i.val=
      quotientEncode faces cycles (value r) i := by
  change value (coefficients (quotientRows faces cycles) (reduce (basis faces) r)) i.val=_
  rw [coefficients_value,value_reduce]
  rfl

theorem liftQuotient_value (faces cycles : List Row) (bits : Row) :
    value (liftQuotient (prepareQuotient faces cycles) bits)=
      quotientLift faces cycles (finiteValue (quotientRows faces cycles).length bits) :=
  linearCombination_value _ _

end PlanarHom.SurfaceBooleanRows
