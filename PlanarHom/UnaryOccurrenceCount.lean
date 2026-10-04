import PlanarHom.MixedUnaryParallelMachines
import PlanarHom.UnaryMarkedCount

/-! Actual binary and unary counts of selected unary occurrences, including
repeated labels at the same vertex and excluding every unselected label. -/
namespace PlanarHom.Complexity.MixedCode
open Turing PlanarHom.BinaryArithmetic

def unaryMarkedCount (selected : ℕ) (g : MixedCode) : ℕ:=
  (g.unaries.filter (fun u=>decide (u.2=selected))).length

private theorem complement_unary_length (selected : ℕ) (us : List (ℕ × ℕ)) :
    (repeatSelected (fun u=>decide (u.2=selected)) 0 us).length+
      (us.filter (fun u=>decide (u.2=selected))).length=us.length:=by
  induction us with
  | nil=>rfl
  | cons u us ih=>
    by_cases h:u.2=selected <;> simp [repeatSelected_cons,h] <;> omega

theorem unaryMarkedCount_eq_sub (selected : ℕ) (g : MixedCode) :
    g.unaryMarkedCount selected=g.unaries.length-(g.parallelUnaryLabel selected 0).unaries.length:=by
  have h:=complement_unary_length selected g.unaries
  change (g.unaries.filter _).length=g.unaries.length-(repeatSelected _ 0 g.unaries).length
  omega

theorem unaryMarkedCount_le_input (selected : ℕ) (g : MixedCode) :
    g.unaryMarkedCount selected≤(encoding.encode g).length:=
  (List.length_filter_le _ _).trans (unaries_le_length g)

theorem fp_unaryMarkedCount_binary (selected : ℕ) :
    FP encoding BitEncoding.nat (unaryMarkedCount selected):=by
  have hc:=fp_unaries.comp (ListCodecMachines.fp_length (BitEncoding.nat.prod BitEncoding.nat))
  have hd:=((fp_const encoding BitEncoding.unaryNat 0).pair (fp_id encoding)).comp
    (fp_parallelUnaryLabel selected)
  exact ((hc.pair (hd.comp hc)).comp fp_subtraction).congr
    (fun g=>(unaryMarkedCount_eq_sub selected g).symm)

theorem fp_unaryMarkedCount_unary (selected : ℕ) :
    FP encoding BitEncoding.unaryNat (unaryMarkedCount selected):=by
  have hlen : FP encoding BitEncoding.unaryNat (fun g=>(encoding.encode g).length):=
    ⟨PlanarHom.InputLengthMachine.computer encoding⟩
  have h:=((hlen.pair (fp_unaryMarkedCount_binary selected)).comp
    (show FP (BitEncoding.unaryNat.prod BitEncoding.nat) BitEncoding.unaryNat
      (fun p=>min p.1 p.2) from ⟨PlanarHom.BoundedUnaryMachines.computer⟩))
  exact h.congr (fun g=>min_eq_right (unaryMarkedCount_le_input selected g))

end PlanarHom.Complexity.MixedCode
