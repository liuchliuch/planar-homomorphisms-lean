import PlanarHom.OccurrencePfaffianListStep
import Mathlib.Data.Nat.Bits
import PlanarHom.OccurrenceKasteleynOrientationLog

/-! NEW reconstruction. Actual exact occurrence counting and even-parity
orientation evaluation, with duplicate log entries toggling repeatedly. -/
namespace PlanarHom.PfaffianList
open Complexity PairProjectionMachines

 theorem fp_occurrenceCount : FP (BitEncoding.nat.list.prod BitEncoding.nat) BitEncoding.nat
    (fun p : List ℕ × ℕ => p.1.count p.2) := by
  have hx := fp_fst BitEncoding.nat.list BitEncoding.nat
  have hk := fp_snd BitEncoding.nat.list BitEncoding.nat
  have hf := (hk.pair hx).comp
    (fp_filterContext BitEncoding.nat BitEncoding.nat (fun p : ℕ × ℕ => decide (p.2=p.1))
      ((fp_nat_eq).congr (fun p => by simp [eq_comm])))
  exact (hf.comp (ListCodecMachines.fp_length BitEncoding.nat)).congr (fun p => by
    simp only [Function.comp_apply, filterContext_eq, List.count_eq_length_filter]
    congr 2
    )

 theorem fp_evenCount : FP (BitEncoding.nat.list.prod BitEncoding.nat) BitEncoding.bool
    (fun p : List ℕ × ℕ => !((p.1.count p.2).bodd)) := by
  let ei := BitEncoding.nat.list.prod BitEncoding.nat
  have hd := (fp_occurrenceCount.pair (fp_const ei BitEncoding.nat 2)).comp
    BinaryArithmetic.fp_division
  have he := (hd.comp (fp_snd BitEncoding.nat BitEncoding.nat)).comp RationalCircuits.fp_nat_isZero
  exact he.congr (fun p => by
    simp only [Function.comp_apply, Nat.mod_two_of_bodd]
    cases (p.1.count p.2).bodd <;> rfl)

end PlanarHom.PfaffianList

namespace PlanarHom.MultiGraph.Kasteleyn
open Complexity
 theorem fp_logOrientation : FP (logCode.prod BitEncoding.nat) BitEncoding.bool
    (fun p : List ℕ × ℕ => logOrientation p.1 p.2) := PfaffianList.fp_evenCount
end PlanarHom.MultiGraph.Kasteleyn
