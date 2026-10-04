import PlanarHom.ListFlattenMachines
import PlanarHom.ConditionalMachines

/-! # Actual typed filtering with a polynomial-time Boolean predicate -/
namespace PlanarHom.ListFilterMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines ListFlattenMachines

variable {α : Type}

def filterStep (p : α→Bool) (acc : List α) (a : α) : List α := if p a then acc++[a] else acc

theorem fold_filterStep (p : α→Bool) (z xs : List α) :
    xs.foldl (filterStep p) z = z++xs.filter p := by
  induction xs generalizing z with
  | nil => simp
  | cons a xs ih =>
    cases hp : p a <;> simp [filterStep,hp,ih,List.append_assoc]

theorem fp_filterStep (e : BitEncoding α) (p : α→Bool) (hp : FP e BitEncoding.bool p) :
    FP (e.list.prod e) e.list (fun q => filterStep p q.1 q.2) := by
  have hz := fp_fst e.list e
  have ha := fp_snd e.list e
  have hsingle := (ha.pair (fp_const (e.list.prod e) e.list [])).comp (ListMutationMachines.fp_cons e)
  have hadd := (hz.pair hsingle).comp (ListMutationMachines.fp_append e)
  have hpred : FP (e.list.prod e) BitEncoding.bool (fun q => decide (p q.2=true)) :=
    (ha.comp hp).congr (fun q => by simp)
  exact hpred.ite hadd hz

theorem payloadSize_filter_le (e : BitEncoding α) (p : α→Bool) (xs : List α) :
    payloadSize e (xs.filter p)≤payloadSize e xs := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases hp : p a <;>
      simp [hp,payloadSize,BitEncoding.frames] at ih ⊢ <;> omega

theorem payloadSize_take_le (e : BitEncoding α) (xs : List α) (i : ℕ) :
    payloadSize e (xs.take i)≤payloadSize e xs := by
  have h := congrArg (payloadSize e) (List.take_append_drop i xs)
  rw [payloadSize_append] at h
  omega

/-- Retained elements consume no more framed payload than the input; canonical
binary count headers are also charged by this linear prefix invariant. -/
theorem prefix_size_bound (e : BitEncoding α) (p : α→Bool) (z xs : List α) (i : ℕ) :
    (e.list.encode ((xs.take i).foldl (filterStep p) z)).length≤
      (Polynomial.C 3*Polynomial.X+1).eval ((e.list.prod e.list).encode (z,xs)).length := by
  have hsum : payloadSize e (z++(xs.take i).filter p)≤((e.list.prod e.list).encode (z,xs)).length := by
    have hz := payloadSize_le_word e z
    have hx := payloadSize_le_word e xs
    have hf := (payloadSize_filter_le e p (xs.take i)).trans (payloadSize_take_le e xs i)
    rw [payloadSize_append,BitEncoding.prod_length]
    dsimp only
    omega
  rw [fold_filterStep]
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one] using
    (word_length_le_payload e _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hsum) 1)

theorem fp_fold_filter (e : BitEncoding α) (p : α→Bool) (hp : FP e BitEncoding.bool p) :
    FP (e.list.prod e.list) e.list (fun q : List α×List α => q.1++q.2.filter p) := by
  exact (ListFoldMachines.fp_foldl e e.list (filterStep p) (fp_filterStep e p hp)
    (Polynomial.C 3*Polynomial.X+1) (fun z xs i _ => prefix_size_bound e p z xs i)).congr
    (fun q => fold_filterStep p q.1 q.2)

/-- The predicate, both materialized branches, selection, and the bounded fold
are all compiled ordinary TM2 programs under the exact canonical list codec. -/
theorem fp_filter (e : BitEncoding α) (p : α→Bool) (hp : FP e BitEncoding.bool p) :
    FP e.list e.list (List.filter p) := by
  exact (((fp_const e.list e.list []).pair (fp_id e.list)).comp (fp_fold_filter e p hp)).congr
    (fun xs => by simp)

end PlanarHom.ListFilterMachines
