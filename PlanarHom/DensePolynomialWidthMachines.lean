import PlanarHom.ListPredicateMachines
import PlanarHom.ListUnaryLengthMachine
import PlanarHom.UnaryNatConversionMachine
import PlanarHom.BinarySubtractionMachine
import PlanarHom.ConditionalMachines

/-! A genuine longest-list selector for dense polynomial axis widths.
The returned list is an existing input, so the fold has a linear prefix bound.
Using maximum rather than summed widths prevents repeated padding blow-up. -/
namespace PlanarHom.DensePolynomial
open Complexity PairProjectionMachines ListFlattenMachines
variable {A : Type}

def wider (a b : List A) : List A := if a.length<b.length then b else a

def longest (xs : List (List A)) : List A := xs.foldl wider []
def width (xs : List (List A)) : ℕ := (longest xs).length

theorem fold_wider_choice (xs : List (List A)) (z : List A) :
    xs.foldl wider z=z ∨ xs.foldl wider z∈xs := by
  induction xs generalizing z with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    rw [List.foldl_cons]
    rcases ih (wider z x) with h|h
    · rw [h]
      unfold wider
      split_ifs
      · exact Or.inr (List.mem_cons_self)
      · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem wider_length_left (a b : List A) : a.length≤(wider a b).length := by
  unfold wider
  split_ifs with h
  · exact h.le
  · rfl

theorem wider_length_right (a b : List A) : b.length≤(wider a b).length := by
  unfold wider
  split_ifs with h
  · rfl
  · exact Nat.le_of_not_gt h

theorem fold_wider_length_initial (xs : List (List A)) (z : List A) :
    z.length≤(xs.foldl wider z).length := by
  induction xs generalizing z with
  | nil => exact le_rfl
  | cons x xs ih => exact (wider_length_left z x).trans (ih _)

theorem fold_wider_length_member (xs : List (List A)) (z x : List A) (hx : x∈xs) :
    x.length≤(xs.foldl wider z).length := by
  induction xs generalizing z with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl|hx
    · exact (wider_length_right z x).trans (fold_wider_length_initial ys _)
    · exact ih _ hx

theorem length_le_width (xs : List (List A)) (x : List A) (hx : x∈xs) : x.length≤width xs :=
  fold_wider_length_member xs [] x hx

theorem fp_wider (e : BitEncoding A) :
    FP (e.list.prod e.list) e.list (fun p=>wider p.1 p.2) := by
  have hl:=fp_fst e.list e.list
  have hr:=fp_snd e.list e.list
  have hn:=(ListUnaryLengthMachine.fp_length e).comp UnaryNatConversionMachine.fp_conversion
  have hp:=((hl.comp hn).pair (hr.comp hn)).comp BinaryArithmetic.fp_comparison
  exact hp.ite hr hl

private theorem element_code_le {A : Type} (e : BitEncoding A) {xs : List A} {x : A} (hx:x∈xs) :
    (e.encode x).length≤(e.list.encode xs).length := by
  have hs:=List.single_le_sum (l:=xs.map (fun a=>(e.encode a).length))
    (fun y _=>Nat.zero_le y) (e.encode x).length (List.mem_map.mpr ⟨x,hx,rfl⟩)
  have hp:=payloadSize_le_word e xs
  rw [payloadSize_eq] at hp
  omega

theorem fp_fold_wider (e : BitEncoding A) :
    FP (e.list.prod e.list.list) e.list (fun p=>p.2.foldl wider p.1) := by
  apply ListFoldMachines.fp_foldl e.list e.list wider (fp_wider e) Polynomial.X
  intro z xs k hk
  have hb : (e.list.encode ((xs.take k).foldl wider z)).length≤
      (e.list.encode z).length+(e.list.list.encode xs).length := by
    rcases fold_wider_choice (xs.take k) z with h|h
    · rw [h]
      omega
    · exact (element_code_le e.list (List.mem_of_mem_take h)).trans (by omega)
  simp only [Polynomial.eval_X,BitEncoding.prod_length]
  omega

theorem fp_longest (e : BitEncoding A) : FP e.list.list e.list longest :=
  ((fp_const e.list.list e.list []).pair (fp_id e.list.list)).comp (fp_fold_wider e)

theorem fp_width (e : BitEncoding A) : FP e.list.list BitEncoding.unaryNat width :=
  (fp_longest e).comp (ListUnaryLengthMachine.fp_length e)

end PlanarHom.DensePolynomial
