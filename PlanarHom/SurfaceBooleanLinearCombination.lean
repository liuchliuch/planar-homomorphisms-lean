import PlanarHom.SurfaceBooleanCoordinateMachines
import PlanarHom.SurfaceBooleanFiniteRows

/-! NEW executable linear combinations of computed rows, with exact semantics
and total polynomial encoded runtime. -/
namespace PlanarHom.SurfaceBooleanRows
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives Polynomial
open scoped BigOperators

def sumRows (rs : List Row) : Row := rs.foldl xorRows []

def linearCombination (bs : BasisRows) (bits : Row) : Row :=
  sumRows (bs.zipIdx.map (fun p => if bitAt bits p.2 then p.1.2 else []))

theorem fold_xorRows_value (rs : List Row) (z : Row) :
    value (rs.foldl xorRows z)=value z+(rs.map value).sum := by
  induction rs generalizing z with
  | nil => simp
  | cons r rs ih => simp [ih,value_xorRows,add_assoc]

theorem sumRows_value (rs : List Row) : value (sumRows rs)=(rs.map value).sum := by
  simp [sumRows,fold_xorRows_value]

theorem linearCombination_value (bs : BasisRows) (bits : Row) :
    value (linearCombination bs bits)=reconstruct bs (finiteValue bs.length bits) := by
  rw [linearCombination,sumRows_value,reconstruct_apply]
  have he : ((bs.zipIdx.map (fun p => if bitAt bits p.2 then p.1.2 else [])).map value)=
      List.ofFn (fun i:Fin bs.length => finiteValue bs.length bits i • rowVectors bs i) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hib : i<bs.length := by simpa using hi
      simp only [List.getElem_map,List.getElem_zipIdx,List.getElem_ofFn,Nat.zero_add]
      change value (if bitAt bits i then (bs[i]).2 else [])=
        bitValue (bitAt bits i)•value (bs[i]).2
      cases bitAt bits i <;> simp [bitValue]
  rw [he,List.sum_ofFn]

theorem fold_xorRows_length (N : ℕ) (rs : List Row) (z : Row)
    (hz : z.length≤N) (hr : ∀r∈rs,r.length≤N) : (rs.foldl xorRows z).length≤N := by
  induction rs generalizing z with
  | nil => exact hz
  | cons r rs ih =>
      apply ih (xorRows z r)
      · rw [xorRows_length]
        exact max_le hz (hr r (by simp))
      · intro s hs
        exact hr s (by simp [hs])

theorem fp_sumRows : FP rowCode.list rowCode sumRows := by
  have hf := ListFoldMachines.fp_foldl rowCode rowCode xorRows fp_xorRows (C 10*(X+1)) (by
    intro z rs i hi
    let N := ((rowCode.prod rowCode.list).encode (z,rs)).length
    have hN : N=2*(rowCode.encode z).length+(rowCode.list.encode rs).length+1 :=
      BitEncoding.prod_length _ _ _
    have hz : z.length≤N := (BitEncoding.list_length_le BitEncoding.bool z).trans (by
      dsimp only [rowCode] at *;omega)
    have hr : ∀r∈rs,r.length≤N := by
      intro r hr
      have he := PlanarityParitySolver.encoded_element_le rowCode hr
      have hl := BitEncoding.list_length_le BitEncoding.bool r
      dsimp only [rowCode] at *
      omega
    have hl := fold_xorRows_length N (rs.take i) z hz (fun r h => hr r (List.mem_of_mem_take h))
    have he := row_encode_le ((rs.take i).foldl xorRows z)
    simp only [eval_mul,eval_C,eval_add,eval_X,eval_one]
    change _≤10*(N+1)
    omega)
  exact ((fp_const rowCode.list rowCode []).pair (fp_id rowCode.list)).comp hf

theorem fp_linearCombination : FP (basisCode.prod rowCode) rowCode
    (fun p => linearCombination p.1 p.2) := by
  let ep := pivotCode.prod BitEncoding.nat
  have hbits := fp_fst rowCode ep
  have hp := fp_snd rowCode ep
  have hi := hp.comp (fp_snd pivotCode BitEncoding.nat)
  have hr := (hp.comp (fp_fst pivotCode BitEncoding.nat)).comp (fp_snd BitEncoding.nat rowCode)
  have ht : FP (rowCode.prod ep) BitEncoding.bool (fun p => decide (bitAt p.1 p.2.2=true)) :=
    ((hbits.pair hi).comp fp_bitAt).congr (fun p => by simp)
  have hv := ht.ite hr (fp_const (rowCode.prod ep) rowCode [])
  have hxs := (fp_fst basisCode rowCode).comp (ListIndexMachines.fp_zipIdx pivotCode)
  have hbs := fp_snd basisCode rowCode
  exact ((hbs.pair hxs).comp (ListContextMachines.fp_mapWithContext rowCode ep rowCode _ hv)).comp fp_sumRows

end PlanarHom.SurfaceBooleanRows
