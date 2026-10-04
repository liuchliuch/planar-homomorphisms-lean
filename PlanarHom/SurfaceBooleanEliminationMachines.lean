import PlanarHom.SurfaceBooleanRowMachines

/-! NEW polynomial size bounds for every actual elimination prefix, followed
by the encoded FP fold. This includes arbitrary malformed initial pivot rows. -/
namespace PlanarHom.SurfaceBooleanRows
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives ListFlattenMachines Polynomial

theorem row_encode_le (r : Row) : (rowCode.encode r).length≤9*r.length+1 := by
  have hs : (r.map (fun a => (BitEncoding.bool.encode a).length)).sum=r.length := by
    induction r with
    | nil => rfl
    | cons a r ih => simp [BitEncoding.bool,ih,Nat.add_comm]
  have h := word_length_le_payload BitEncoding.bool r
  rw [payloadSize_eq,hs] at h
  change (rowCode.encode r).length≤3*(2*r.length+r.length)+1 at h
  omega

theorem clear_length_le {N : ℕ} (r : Row) (p : PivotRow)
    (hr : r.length≤N) (hp : p.2.length≤N) : (clear r p).length≤N := by
  unfold clear
  split
  · rw [xorRows_length]; omega
  · exact hr

theorem reduce_length_le {N : ℕ} (bs : BasisRows) (r : Row)
    (hr : r.length≤N) (hbs : ∀p∈bs,p.2.length≤N) : (reduce bs r).length≤N := by
  induction bs generalizing r with
  | nil => exact hr
  | cons p bs ih =>
      exact ih (clear r p) (clear_length_le r p hr (hbs p (by simp)))
        (fun q hq => hbs q (by simp [hq]))

theorem fp_reduce : FP (rowCode.prod basisCode) rowCode (fun p => reduce p.2 p.1) := by
  apply ListFoldMachines.fp_foldl pivotCode rowCode clear fp_clear (C 10*(X+1))
  intro r bs i hi
  let N := ((rowCode.prod basisCode).encode (r,bs)).length
  have hN : N=2*(rowCode.encode r).length+(basisCode.encode bs).length+1 :=
    BitEncoding.prod_length _ _ _
  have hr : r.length≤N := (BitEncoding.list_length_le BitEncoding.bool r).trans (by
    dsimp only [rowCode,basisCode,pivotCode] at *
    omega)
  have hb : ∀p∈bs,p.2.length≤N := by
    intro p hp
    have he := PlanarityParitySolver.encoded_element_le pivotCode hp
    have hw := BitEncoding.list_length_le BitEncoding.bool p.2
    simp only [pivotCode,BitEncoding.prod_length] at he
    dsimp only [rowCode,basisCode,pivotCode] at *
    omega
  have hl := reduce_length_le (bs.take i) r hr (fun p hp => hb p (List.mem_of_mem_take hp))
  have hc := row_encode_le (reduce (bs.take i) r)
  simp only [eval_mul,eval_C,eval_add,eval_X,eval_one]
  change _≤10*(N+1)
  change (rowCode.encode (reduce (bs.take i) r)).length≤_
  omega

theorem fp_addRow : FP (basisCode.prod rowCode) basisCode (fun p => addRow p.1 p.2) := by
  have hb := fp_fst basisCode rowCode
  have hr := fp_snd basisCode rowCode
  have hs := (hr.pair hb).comp fp_reduce
  have hi := hs.comp fp_pivot
  have hl := hs.comp (ListCodecMachines.fp_length BitEncoding.bool)
  have htest := (hi.pair hl).comp BinaryArithmetic.fp_comparison
  have hp := (hi.pair hs).pair (fp_const (basisCode.prod rowCode) basisCode [])
  have hsingle := hp.comp (ListMutationMachines.fp_cons pivotCode)
  exact htest.ite ((hb.pair hsingle).comp (ListMutationMachines.fp_append pivotCode)) hb

def WidthBound (N : ℕ) (bs : BasisRows) : Prop :=
  ∀p∈bs,p.2.length≤N ∧ (BitEncoding.nat.encode p.1).length≤N

theorem width_addRow {N : ℕ} (bs : BasisRows) (r : Row)
    (hb : WidthBound N bs) (hr : r.length≤N) : WidthBound N (addRow bs r) := by
  dsimp only [addRow]
  split
  · rename_i hp
    intro p hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hb p hmem
    · have he : p=(pivot (reduce bs r),reduce bs r) := by simpa using hmem
      subst p
      have hl := reduce_length_le bs r hr (fun p h => (hb p h).1)
      exact ⟨hl,(encodeNat_length_le _).trans (Nat.le_of_lt hp |>.trans hl)⟩
  · exact hb

theorem addRow_length_le (bs : BasisRows) (r : Row) : (addRow bs r).length≤bs.length+1 := by
  dsimp only [addRow]
  split <;> simp <;> omega

theorem fold_addRow_bounds {N : ℕ} (rs : List Row) (bs : BasisRows)
    (hb : WidthBound N bs) (hr : ∀r∈rs,r.length≤N) :
    WidthBound N (rs.foldl addRow bs) ∧ (rs.foldl addRow bs).length≤bs.length+rs.length := by
  induction rs generalizing bs with
  | nil => exact ⟨hb,by simp⟩
  | cons r rs ih =>
      have ht := ih (addRow bs r) (width_addRow bs r hb (hr r (by simp)))
        (fun s hs => hr s (by simp [hs]))
      refine ⟨ht.1,?_⟩
      have hl := addRow_length_le bs r
      simp only [List.foldl_cons,List.length_cons]
      omega

theorem basis_encode_le {N : ℕ} (bs : BasisRows) (hb : WidthBound N bs)
    (hl : bs.length≤2*N) : (basisCode.encode bs).length≤200*(N+1)^2 := by
  have hw : ∀p∈bs,(pivotCode.encode p).length≤11*N+2 := by
    intro p hp
    have hb' := hb p hp
    have hr := row_encode_le p.2
    simp only [pivotCode,BitEncoding.prod_length]
    omega
  have hs := ListMapMachines.sum_map_le_mul (fun p => (pivotCode.encode p).length) bs (11*N+2) hw
  have hm := Nat.mul_le_mul_right (11*N+2) hl
  have he := word_length_le_payload pivotCode bs
  rw [payloadSize_eq] at he
  change (pivotCode.list.encode bs).length≤_
  nlinarith

theorem fp_extendBasis : FP (basisCode.prod rowCode.list) basisCode
    (fun p => p.2.foldl addRow p.1) := by
  apply ListFoldMachines.fp_foldl rowCode basisCode addRow fp_addRow (C 200*(X+1)^2)
  intro bs rs i hi
  let N := ((basisCode.prod rowCode.list).encode (bs,rs)).length
  have hN : N=2*(basisCode.encode bs).length+(rowCode.list.encode rs).length+1 :=
    BitEncoding.prod_length _ _ _
  have hb : WidthBound N bs := by
    intro p hp
    have he := PlanarityParitySolver.encoded_element_le pivotCode hp
    have hr := BitEncoding.list_length_le BitEncoding.bool p.2
    simp only [pivotCode,BitEncoding.prod_length] at he
    dsimp only [rowCode,basisCode,pivotCode] at *
    constructor <;> omega
  have hr : ∀r∈rs,r.length≤N := by
    intro r hr
    have he := PlanarityParitySolver.encoded_element_le rowCode hr
    have hl := BitEncoding.list_length_le BitEncoding.bool r
    dsimp only [rowCode,basisCode,pivotCode] at *
    omega
  have hlenb := BitEncoding.list_length_le pivotCode bs
  have hlenr := BitEncoding.list_length_le rowCode rs
  have ht := fold_addRow_bounds (rs.take i) bs hb (fun r h => hr r (List.mem_of_mem_take h))
  have htake : (rs.take i).length≤rs.length := by simp
  have hsize := basis_encode_le ((rs.take i).foldl addRow bs) ht.1 (by
    dsimp only [rowCode,basisCode,pivotCode] at *
    omega)
  simpa only [eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one] using hsize

theorem fp_basis : FP rowCode.list basisCode basis :=
  ((fp_const rowCode.list basisCode []).pair (fp_id rowCode.list)).comp fp_extendBasis

end PlanarHom.SurfaceBooleanRows
