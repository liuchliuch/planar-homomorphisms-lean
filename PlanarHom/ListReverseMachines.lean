import PlanarHom.ListFilterMachines

/-! Actual canonical list reversal, including bounded intermediate framing. -/
namespace PlanarHom.ListReverseMachines
open PlanarHom.Complexity PlanarHom.ListFlattenMachines Polynomial

private theorem prefix_bound {α : Type} (e : BitEncoding α) (z xs : List α) (i : ℕ) :
    (e.list.encode ((xs.take i).foldl (fun acc a=>a::acc) z)).length≤
      (C 3*X+1).eval ((e.list.prod e.list).encode (z,xs)).length:=by
  have ht:=PlanarHom.ListFilterMachines.payloadSize_take_le e xs i
  have hz:=payloadSize_le_word e z
  have hx:=payloadSize_le_word e xs
  have hr : payloadSize e (xs.take i).reverse=payloadSize e (xs.take i):=by
    simp [payloadSize_eq,List.map_reverse]
  rw [List.foldl_flip_cons_eq_append']
  have hp : payloadSize e ((xs.take i).reverse++z)≤((e.list.prod e.list).encode (z,xs)).length:=by
    rw [payloadSize_append,hr,BitEncoding.prod_length]
    dsimp only
    omega
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one] using
    (word_length_le_payload e _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hp) 1)

theorem fp_reverse {α : Type} (e : BitEncoding α) : FP e.list e.list List.reverse:=by
  have hs:=(PairProjectionMachines.fp_snd e.list e).pair (PairProjectionMachines.fp_fst e.list e)
  have hb:=hs.comp (PlanarHom.ListMutationMachines.fp_cons e)
  have hf:=PlanarHom.ListFoldMachines.fp_foldl e e.list (fun acc a=>a::acc) hb
    (C 3*X+1) (fun z xs i _=>prefix_bound e z xs i)
  exact (((fp_const e.list e.list []).pair (fp_id e.list)).comp hf).congr
    (fun xs=>by simp)

end PlanarHom.ListReverseMachines
