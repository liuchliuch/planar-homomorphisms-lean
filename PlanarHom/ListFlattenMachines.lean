import PlanarHom.ListFoldMachines

/-! # Actual typed list flattening, via a size-bounded append fold -/
namespace PlanarHom.ListFlattenMachines
open Complexity ArithmeticCircuitPrimitives BinaryArithmetic

/-- Size of the fully framed payload, excluding the binary length header. -/
def payloadSize {α : Type} (e : BitEncoding α) (xs : List α) : ℕ :=
  (BitEncoding.frames (xs.map e.encode)).length

theorem payloadSize_eq {α : Type} (e : BitEncoding α) (xs : List α) :
    payloadSize e xs=2*(xs.map (fun a => (e.encode a).length)).sum+xs.length := by
  simp [payloadSize,BitEncoding.frames_length,List.map_map,Function.comp_def]

theorem payloadSize_append {α : Type} (e : BitEncoding α) (xs ys : List α) :
    payloadSize e (xs++ys)=payloadSize e xs+payloadSize e ys := by
  simp only [payloadSize_eq,List.map_append,List.sum_append,List.length_append]
  omega

theorem payloadSize_le_word {α : Type} (e : BitEncoding α) (xs : List α) :
    payloadSize e xs≤(e.list.encode xs).length := by
  simp [BitEncoding.list,payloadSize]

theorem word_length_le_payload {α : Type} (e : BitEncoding α) (xs : List α) :
    (e.list.encode xs).length≤3*payloadSize e xs+1 := by
  have hn : (BitEncoding.nat.encode xs.length).length≤xs.length := by
    change (Computability.encodeNat xs.length).length≤xs.length
    rw [encodeNat_length]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hs : xs.length≤payloadSize e xs := by rw [payloadSize_eq]; omega
  change (BitEncoding.frame (BitEncoding.nat.encode xs.length) ++ BitEncoding.frames (xs.map e.encode)).length≤_
  rw [List.length_append,BitEncoding.frame_length]
  change 2*(BitEncoding.nat.encode xs.length).length+1+payloadSize e xs≤_
  omega

theorem fold_append_payload {α : Type} (e : BitEncoding α) (z : List α) (xs : List (List α)) :
    payloadSize e (xs.foldl (fun acc a => acc++a) z) = payloadSize e z+(xs.map (payloadSize e)).sum := by
  induction xs generalizing z with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons,ih,payloadSize_append,List.map_cons,List.sum_cons]
    omega

theorem sum_take_le {α : Type} (g : α→ℕ) (xs : List α) (i : ℕ) :
    ((xs.take i).map g).sum≤(xs.map g).sum := by
  have h := congrArg (fun ys => (ys.map g).sum) (List.take_append_drop i xs)
  simp only [List.map_append,List.sum_append] at h
  omega

/-- Every intermediate flattened prefix has linear encoded size in the entire
input, including an arbitrary starting list. -/
theorem prefix_size_bound {α : Type} (e : BitEncoding α) (z : List α) (xs : List (List α)) (i : ℕ) :
    (e.list.encode ((xs.take i).foldl (fun acc a => acc++a) z)).length ≤
      (Polynomial.C 3*Polynomial.X+Polynomial.C 1).eval ((e.list.prod e.list.list).encode (z,xs)).length := by
  let N := ((e.list.prod e.list.list).encode (z,xs)).length
  have hp : N=2*(e.list.encode z).length+(e.list.list.encode xs).length+1 := BitEncoding.prod_length _ _ _
  have hx : (e.list.list.encode xs).length =
      2*(BitEncoding.nat.encode xs.length).length+1+2*(xs.map (fun a => (e.list.encode a).length)).sum+xs.length := by
    simp [BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
    omega
  have hz := payloadSize_le_word e z
  have ht := sum_take_le (payloadSize e) xs i
  have hs : (xs.map (payloadSize e)).sum ≤ (xs.map (fun a => (e.list.encode a).length)).sum :=
    List.sum_le_sum (fun a _ => payloadSize_le_word e a)
  have hpayload : payloadSize e ((xs.take i).foldl (fun acc a => acc++a) z)≤N := by
    rw [fold_append_payload]
    omega
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using
    (word_length_le_payload e _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hpayload) 1)

theorem fold_append_eq {α : Type} (z : List α) (xs : List (List α)) :
    xs.foldl (fun acc a => acc++a) z = z++xs.flatten := by
  induction xs generalizing z with
  | nil => simp
  | cons a xs ih => simp [ih,List.append_assoc]

/-- Append a dynamically many number of lists to an initial accumulator. -/
theorem fp_fold_append {α : Type} (e : BitEncoding α) :
    FP (e.list.prod e.list.list) e.list (fun p : List α×List (List α) => p.1++p.2.flatten) := by
  exact (ListFoldMachines.fp_foldl e.list e.list (fun acc a => acc++a)
    (ListMutationMachines.fp_append e) (Polynomial.C 3*Polynomial.X+Polynomial.C 1)
    (fun z xs i _ => prefix_size_bound e z xs i)).congr (fun p => fold_append_eq p.1 p.2)

/-- Actual ordinary-machine flattening for the project's exact nested-list codec. -/
theorem fp_flatten {α : Type} (e : BitEncoding α) :
    FP e.list.list e.list (List.flatten : List (List α)→List α) := by
  exact (((fp_const e.list.list e.list []).pair (fp_id e.list.list)).comp
    (fp_fold_append e)).congr (fun xs => by simp)

end PlanarHom.ListFlattenMachines
