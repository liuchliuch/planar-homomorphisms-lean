import PlanarHom.ListDecompositionMachines
import PlanarHom.ListDedupMachines
import PlanarHom.ListUnaryLengthMachine
import PlanarHom.RestrictedIterationMachine

/-! Runtime list suffix selection with a binary index. Its unary loop count is
bounded by the literal input list length, so arbitrarily large indices are safe. -/
noncomputable section
namespace PlanarHom.ListDropMachines
open Complexity PairProjectionMachines MachineComposition ListFlattenMachines
variable {A : Type}

theorem iterate_tail (xs : List A) (n : ℕ) : List.tail^[n] xs = xs.drop n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp

theorem fp_dropUnary (e : BitEncoding A) (d : A) :
    FP (BitEncoding.unaryNat.prod e.list) e.list
      (fun p : ℕ × List A => p.2.drop p.1) := by
  obtain ⟨body⟩ := ListDecompositionMachines.fp_tail e d
  let p : Polynomial ℕ := Polynomial.C 3 * Polynomial.X + 1
  have hb (n : ℕ) (xs : List A) (i : ℕ) (_ : i ≤ n) :
      (e.list.encode (List.tail^[i] xs)).length ≤
        p.eval ((BitEncoding.unaryNat.prod e.list).encode (n,xs)).length := by
    rw [iterate_tail]
    have hp := ListDedupMachines.payloadSize_sublist e (List.drop_sublist i xs)
    have hw := word_length_le_payload e (xs.drop i)
    have hx := payloadSize_le_word e xs
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one, BitEncoding.prod_length,
      BitEncoding.unaryNat_length]
    omega
  exact (show FP (BitEncoding.unaryNat.prod e.list) e.list
    (fun p : ℕ × List A => List.tail^[p.1] p.2) from
      ⟨BoundedIterationMachine.computer e.list List.tail body p hb⟩).congr
        (fun p => iterate_tail p.2 p.1)

/-- Exact total binary-index suffix operation. -/
theorem fp_drop (e : BitEncoding A) (d : A) :
    FP (BitEncoding.nat.prod e.list) e.list
      (fun p : ℕ × List A => p.2.drop p.1) := by
  have hn := fp_fst BitEncoding.nat e.list
  have hxs := fp_snd BitEncoding.nat e.list
  have hl := hxs.comp (ListUnaryLengthMachine.fp_length e)
  have hc := (hl.pair hn).comp (show FP (BitEncoding.unaryNat.prod BitEncoding.nat)
    BitEncoding.unaryNat (fun p => min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)
  apply ((hc.pair hxs).comp (fp_dropUnary e d)).congr
  intro p
  simp only [Function.comp_apply]
  by_cases h : p.2.length ≤ p.1
  · rw [min_eq_left h, List.drop_length, List.drop_eq_nil_of_le h]
  · rw [min_eq_right (by omega)]

end PlanarHom.ListDropMachines
