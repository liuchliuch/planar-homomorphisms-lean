import PlanarHom.ListFoldMachines
import PlanarHom.BinaryAdditionMachine
import PlanarHom.BinarySubtractionMachine
import PlanarHom.ArithmeticCircuitPrimitives
import PlanarHom.MachineOutputTransport

/-! Actual natural-list addition and comparison circuits for exponent filtering. -/
namespace PlanarHom.NatListSumMachines
open Turing Polynomial PlanarHom.Complexity PlanarHom.BinaryArithmetic

private theorem addition_length (a b : ℕ) :
    (BitEncoding.nat.encode (a+b)).length≤(BitEncoding.nat.encode a).length+
      (BitEncoding.nat.encode b).length+1:=by
  simpa only [BitEncoding.nat,addBits_encodeNat] using
    addBits_length_le false (Computability.encodeNat a) (Computability.encodeNat b)

private theorem fold_length (xs : List ℕ) (z : ℕ) :
    (BitEncoding.nat.encode (xs.foldl Nat.add z)).length≤(BitEncoding.nat.encode z).length+
      (xs.map (fun x=>(BitEncoding.nat.encode x).length)).sum+xs.length:=by
  induction xs generalizing z with
  | nil=>simp
  | cons x xs ih=>
    have h:=ih (z+x)
    have ha:=addition_length z x
    simp only [List.foldl_cons,Nat.add_eq,List.map_cons,List.sum_cons,List.length_cons]
    omega

private theorem prefix_size (z : ℕ) (xs : List ℕ) (i : ℕ) (_hi : i≤xs.length) :
    (BitEncoding.nat.encode ((xs.take i).foldl Nat.add z)).length≤
      (C 3*X+1).eval ((BitEncoding.nat.prod BitEncoding.nat.list).encode (z,xs)).length:=by
  have h:=fold_length (xs.take i) z
  have hw : ((xs.take i).map (fun x=>(BitEncoding.nat.encode x).length)).sum≤
      (xs.map (fun x=>(BitEncoding.nat.encode x).length)).sum:=by
    have ht := (List.take_sublist i xs).map (fun x=>(BitEncoding.nat.encode x).length)
    exact List.Sublist.sum_le_sum ht (fun _ _=>Nat.zero_le _)
  have hl : (xs.take i).length≤xs.length:=by simp only [List.length_take]; exact Nat.min_le_right _ _
  simp only [BitEncoding.prod_length,BitEncoding.list,List.length_append,BitEncoding.frame_length,
    BitEncoding.frames_length,List.map_map,List.length_map,Function.comp_def,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
  omega

theorem fp_fold_add : FP (BitEncoding.nat.prod BitEncoding.nat.list) BitEncoding.nat
    (fun p : ℕ × List ℕ=>p.2.foldl Nat.add p.1):=
  PlanarHom.ListFoldMachines.fp_foldl BitEncoding.nat BitEncoding.nat Nat.add fp_addition
    (C 3*X+1) prefix_size

theorem fp_sum : FP BitEncoding.nat.list BitEncoding.nat List.sum:=by
  have h:=((fp_const BitEncoding.nat.list BitEncoding.nat 0).pair (fp_id BitEncoding.nat.list)).comp fp_fold_add
  exact h.congr (fun xs=>by
    have he : Nat.add=(fun x y : ℕ=>x+y):=by funext x y; exact Nat.add_eq
    simp [he,List.sum_eq_foldl])

theorem fp_equal : FP (BitEncoding.nat.prod BitEncoding.nat) BitEncoding.bool
    (fun p : ℕ × ℕ=>decide (p.1=p.2)):=by
  have hswap:=(PairProjectionMachines.fp_snd BitEncoding.nat BitEncoding.nat).pair
    (PairProjectionMachines.fp_fst BitEncoding.nat BitEncoding.nat)
  have h:=(fp_comparison.pair (hswap.comp fp_comparison)).comp
    (PlanarHom.ArithmeticCircuitPrimitives.fp_bool_gate (fun p=> !p.1 && !p.2))
  apply h.congr
  intro p
  change (!decide (p.1<p.2) && !decide (p.2<p.1))=decide (p.1=p.2)
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq]
  omega

end PlanarHom.NatListSumMachines
