import PlanarHom.ListContextMachines
import PlanarHom.GraphParallelCode
import Mathlib.Data.List.Enum

/-! Actual occurrence indexing for the existing framed-list codec. The running
index is the length of the materialized accumulator, so it is always bounded by
the input size. Equal list values retain distinct occurrence indices. -/

namespace PlanarHom.ListIndexMachines
open Complexity PairProjectionMachines ListFlattenMachines Polynomial

def step {α : Type} (zs : List (α × ℕ)) (a : α) : List (α × ℕ) :=
  zs ++ [(a,zs.length)]

theorem fold_step {α : Type} (zs : List (α × ℕ)) (xs : List α) :
    xs.foldl step zs = zs ++ xs.zipIdx zs.length := by
  induction xs generalizing zs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons, step, ih, List.length_append, List.length_singleton,
      List.zipIdx_cons, List.append_assoc, List.singleton_append]

theorem fp_step {α : Type} (e : BitEncoding α) :
    FP ((e.prod BitEncoding.nat).list.prod e) (e.prod BitEncoding.nat).list
      (fun p => step p.1 p.2) := by
  let ep := e.prod BitEncoding.nat
  have hz := fp_fst ep.list e
  have ha := fp_snd ep.list e
  have hn := hz.comp (ListCodecMachines.fp_length ep)
  have hi := (ha.pair hn).pair (fp_const (ep.list.prod e) ep.list [])
  exact (hz.pair (hi.comp (ListMutationMachines.fp_cons ep))).comp
    (ListMutationMachines.fp_append ep)

private theorem prefix_bound {α : Type} (e : BitEncoding α)
    (zs : List (α × ℕ)) (xs : List α) (i : ℕ) :
    ((e.prod BitEncoding.nat).list.encode ((xs.take i).foldl step zs)).length ≤
      (C 100*(X+1)^2).eval
        (((e.prod BitEncoding.nat).list.prod e.list).encode (zs,xs)).length := by
  let N := (((e.prod BitEncoding.nat).list.prod e.list).encode (zs,xs)).length
  have hN : N = 2*((e.prod BitEncoding.nat).list.encode zs).length +
      (e.list.encode xs).length + 1 := BitEncoding.prod_length _ _ _
  have hz : zs.length ≤ N :=
    (BitEncoding.list_length_le (e.prod BitEncoding.nat) zs).trans (by omega)
  have hx : xs.length ≤ N := (BitEncoding.list_length_le e xs).trans (by omega)
  have ht : (xs.take i).length ≤ N := by rw [List.length_take]; omega
  have hword : ∀ a ∈ xs, (e.encode a).length ≤ N := by
    intro a ha
    have hh := ListMapMachines.mem_le_sum_map (fun a => (e.encode a).length) ha
    dsimp only at hh
    have hp := payloadSize_le_word e xs
    rw [payloadSize_eq] at hp
    omega
  have hp : ∀ p ∈ (xs.take i).zipIdx zs.length,
      ((e.prod BitEncoding.nat).encode p).length ≤ 4*N+1 := by
    rw [List.forall_mem_zipIdx]
    intro j hj
    have ha := hword ((xs.take i)[j]) (List.mem_of_mem_take (List.getElem_mem hj))
    have hn := encodeNat_length_le (zs.length+j)
    have hj' : j < N := hj.trans_le ht
    rw [BitEncoding.prod_length]
    dsimp only
    omega
  have hs := ListMapMachines.sum_map_le_mul
    (fun p : α × ℕ => ((e.prod BitEncoding.nat).encode p).length)
    ((xs.take i).zipIdx zs.length) (4*N+1) hp
  have hzP : payloadSize (e.prod BitEncoding.nat) zs ≤ N :=
    (payloadSize_le_word _ zs).trans (by omega)
  have hnew : payloadSize (e.prod BitEncoding.nat) ((xs.take i).zipIdx zs.length)
      ≤ 8*N^2+3*N := by
    rw [payloadSize_eq]
    simp only [List.length_zipIdx] at hs ⊢
    have hm := Nat.mul_le_mul_right (4*N+1) ht
    nlinarith
  have hfinal := word_length_le_payload (e.prod BitEncoding.nat)
    (zs ++ (xs.take i).zipIdx zs.length)
  rw [payloadSize_append] at hfinal
  rw [fold_step]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ 100*(N+1)^2
  nlinarith

/-- The machine emits `(value, index)` in original order, with exact zero-based
indices, including duplicate values and the empty list. -/
theorem fp_zipIdx {α : Type} (e : BitEncoding α) :
    FP e.list (e.prod BitEncoding.nat).list (fun xs => xs.zipIdx) := by
  have hf := ListFoldMachines.fp_foldl e (e.prod BitEncoding.nat).list step
    (fp_step e) (C 100*(X+1)^2) (fun zs xs i _ => prefix_bound e zs xs i)
  exact (((fp_const e.list (e.prod BitEncoding.nat).list []).pair
    (fp_id e.list)).comp hf).congr (fun xs => by simp [fold_step])

end PlanarHom.ListIndexMachines
