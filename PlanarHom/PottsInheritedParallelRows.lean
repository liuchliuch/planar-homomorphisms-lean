import PlanarHom.PottsSourceInverseRowMachines
import PlanarHom.ListFlattenMachines

/-! NEW literal inherited parallel-copy rows. Occurrence e gets copies e*t+r.
The true/source dart lists copies increasingly, the false/target dart lists
them decreasingly. These total list programs have unconditional FP machines;
the compatible drawing and Euler identities are proved separately for them. -/
namespace PlanarHom.PottsSourceInverseRows
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives PlanarityRotationCode

def parallelDartBlock (t : ℕ) (a : PlanarityRotationCode.Dart) : List PlanarityRotationCode.Dart :=
  (if a.2 then List.range t else (List.range t).reverse).map (fun r=>(a.1*t+r,a.2))

def parallelRow (t : ℕ) (row : List PlanarityRotationCode.Dart) : List PlanarityRotationCode.Dart :=
  row.flatMap (parallelDartBlock t)

def parallelRows (t : ℕ) (rows : Rows) : Rows := rows.map (parallelRow t)

theorem fp_parallelDartBlock : FP (BitEncoding.unaryNat.prod dartCode) dartCode.list
    (fun p=>parallelDartBlock p.1 p.2) := by
  let ctx := BitEncoding.unaryNat.prod dartCode
  have ht:=fp_fst BitEncoding.unaryNat dartCode
  have ha:=fp_snd BitEncoding.unaryNat dartCode
  have hb:=ha.comp (fp_snd BitEncoding.nat BitEncoding.bool)
  have hr:=ht.comp UnaryArithmeticMachines.fp_range
  have hrev:=hr.comp (ListReverseMachines.fp_reverse BitEncoding.nat)
  have hcond : FP ctx BitEncoding.bool (fun p=>decide (p.2.2=true)) := hb.congr (fun _=>by simp)
  have horder:=hcond.ite hr hrev
  have hc:=fp_fst ctx BitEncoding.nat
  have hi:=fp_snd ctx BitEncoding.nat
  have htc:=(hc.comp ht).comp UnaryNatConversionMachine.fp_conversion
  have he:=(hc.comp ha).comp (fp_fst BitEncoding.nat BitEncoding.bool)
  have hecopy:=(((he.pair htc).comp BinaryArithmetic.fp_multiplication).pair hi).comp BinaryArithmetic.fp_addition
  have hentry:=hecopy.pair (hc.comp hb)
  exact ((fp_id ctx).pair horder).comp
    (ListContextMachines.fp_mapWithContext ctx BitEncoding.nat dartCode _ hentry)

theorem fp_parallelRow : FP (BitEncoding.unaryNat.prod dartCode.list) dartCode.list
    (fun p=>parallelRow p.1 p.2) := by
  have hmap:=ListContextMachines.fp_mapWithContext BitEncoding.unaryNat dartCode dartCode.list
    (fun p=>parallelDartBlock p.1 p.2) fp_parallelDartBlock
  exact (hmap.comp (ListFlattenMachines.fp_flatten dartCode)).congr (fun _=>rfl)

theorem fp_parallelRows : FP (BitEncoding.unaryNat.prod rowsCode) rowsCode
    (fun p=>parallelRows p.1 p.2) :=
  ListContextMachines.fp_mapWithContext BitEncoding.unaryNat dartCode.list dartCode.list
    (fun p=>parallelRow p.1 p.2) fp_parallelRow

@[simp] theorem parallelDartBlock_length (t : ℕ) (a : PlanarityRotationCode.Dart) :
    (parallelDartBlock t a).length=t := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [parallelDartBlock]

@[simp] theorem parallelRows_length (t : ℕ) (rows : Rows) :
    (parallelRows t rows).length=rows.length := by simp [parallelRows]

end PlanarHom.PottsSourceInverseRows
