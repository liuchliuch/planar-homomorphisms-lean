import PlanarHom.SurfaceBooleanEliminationMachines

/-! NEW actual coefficient extraction with an explicit linear bound on every
materialized row/log state. -/
namespace PlanarHom.SurfaceBooleanRows
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives Polynomial
abbrev coefficientStateCode := rowCode.prod rowCode

def coefficientStep (s : Row×Row) (p : PivotRow) : Row×Row :=
  (clear s.1 p,s.2++[bitAt s.1 p.1])

theorem fp_coefficientStep : FP (coefficientStateCode.prod pivotCode) coefficientStateCode
    (fun p => coefficientStep p.1 p.2) := by
  have hs := fp_fst coefficientStateCode pivotCode
  have hr := hs.comp (fp_fst rowCode rowCode)
  have hz := hs.comp (fp_snd rowCode rowCode)
  have hp := fp_snd coefficientStateCode pivotCode
  have hi := hp.comp (fp_fst BitEncoding.nat rowCode)
  have hb := (hr.pair hi).comp fp_bitAt
  have hone := (hb.pair (fp_const _ rowCode [])).comp (ListMutationMachines.fp_cons BitEncoding.bool)
  exact ((hr.pair hp).comp fp_clear).pair
    ((hz.pair hone).comp (ListMutationMachines.fp_append BitEncoding.bool))

theorem coefficient_fold_bounds (N : ℕ) (bs : BasisRows) (s : Row×Row)
    (hr : s.1.length≤N) (hb : ∀p∈bs,p.2.length≤N) :
    (bs.foldl coefficientStep s).1.length≤N ∧
    (bs.foldl coefficientStep s).2.length=s.2.length+bs.length := by
  induction bs generalizing s with
  | nil => exact ⟨hr,by simp⟩
  | cons p bs ih =>
      have ht := ih (coefficientStep s p) (clear_length_le s.1 p hr (hb p (by simp)))
        (fun q hq => hb q (by simp [hq]))
      refine ⟨ht.1,?_⟩
      have hh := ht.2
      simp only [coefficientStep,List.length_append,List.length_singleton,List.length_cons,
        List.foldl_cons,List.length_nil] at hh ⊢
      omega

theorem fp_coefficientFold : FP (coefficientStateCode.prod basisCode) coefficientStateCode
    (fun p => p.2.foldl coefficientStep p.1) := by
  apply ListFoldMachines.fp_foldl pivotCode coefficientStateCode coefficientStep fp_coefficientStep
    (C 40*(X+1))
  intro s bs i hi
  let N := ((coefficientStateCode.prod basisCode).encode (s,bs)).length
  have hN : N=2*(2*(rowCode.encode s.1).length+(rowCode.encode s.2).length+1)+
      (basisCode.encode bs).length+1 := by simp only [coefficientStateCode,BitEncoding.prod_length,N]
  have hr := BitEncoding.list_length_le BitEncoding.bool s.1
  have hz := BitEncoding.list_length_le BitEncoding.bool s.2
  have hb := BitEncoding.list_length_le pivotCode bs
  have hrow : ∀p∈bs,p.2.length≤N := by
    intro p hp
    have he := PlanarityParitySolver.encoded_element_le pivotCode hp
    have hw := BitEncoding.list_length_le BitEncoding.bool p.2
    simp only [pivotCode,BitEncoding.prod_length] at he
    dsimp only [rowCode,basisCode,pivotCode] at *
    omega
  have ht := coefficient_fold_bounds N (bs.take i) s (by
      dsimp only [rowCode,basisCode,pivotCode] at *; omega)
    (fun p hp => hrow p (List.mem_of_mem_take hp))
  have hx := row_encode_le (((bs.take i).foldl coefficientStep s).1)
  have hy := row_encode_le (((bs.take i).foldl coefficientStep s).2)
  have htake : (bs.take i).length≤bs.length := by simp
  simp only [eval_mul,eval_C,eval_add,eval_X,eval_one]
  change (coefficientStateCode.encode ((bs.take i).foldl coefficientStep s)).length≤40*(N+1)
  rw [BitEncoding.prod_length]
  dsimp only [rowCode,basisCode,pivotCode] at *
  omega

theorem fp_coefficients : FP (rowCode.prod basisCode) rowCode (fun p => coefficients p.2 p.1) := by
  have hr := fp_fst rowCode basisCode
  have hb := fp_snd rowCode basisCode
  exact ((((hr.pair (fp_const _ rowCode [])).pair hb).comp fp_coefficientFold).comp
    (fp_snd rowCode rowCode))

end PlanarHom.SurfaceBooleanRows
