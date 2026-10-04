import PlanarHom.ConditionalMachines
import PlanarHom.RationalCircuits
import PlanarHom.RestrictedListFoldMachines
import PlanarHom.ListCodecMachines

/-! Actual total head/default and tail machines for the existing framed list codec. -/

namespace PlanarHom.ListDecompositionMachines
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives BinaryArithmetic
variable {α : Type}
noncomputable section
attribute [local instance] Classical.propDecidable

/-- An empty list is replaced physically by one default item before the nonempty parser. -/
def ensureNonempty (d : α) (xs : List α) : List α := if xs = [] then [d] else xs

theorem ensureNonempty_ne_nil (d : α) (xs : List α) : ensureNonempty d xs ≠ [] := by
  simp only [ensureNonempty]
  split <;> simp_all

abbrev NonemptyList (α : Type) := {xs : List α // xs ≠ []}
noncomputable def nonemptyEncoding (e : BitEncoding α) : BitEncoding (NonemptyList α) :=
  e.list.restrict (fun xs => xs ≠ [])

def prepare (d : α) (xs : List α) : NonemptyList α :=
  ⟨ensureNonempty d xs, ensureNonempty_ne_nil d xs⟩

/-- A real length/zero-test and byte selector prepare the total default case. -/
theorem fp_prepare (e : BitEncoding α) (d : α) :
    FP e.list (nonemptyEncoding e) (prepare d) := by
  classical
  have hp : FP e.list BitEncoding.bool (fun xs : List α => decide (xs = [])) :=
    ((ListCodecMachines.fp_length e).comp RationalCircuits.fp_nat_isZero).congr
      (fun xs => by simp)
  have hn : FP e.list e.list (ensureNonempty d) :=
    hp.ite (fp_const e.list e.list [d]) (fp_id e.list)
  exact hn.transportOutput (fun _ => rfl)

/-- Header removal on the nonempty subtype still uses the actual payload machine. -/
theorem fp_payload (e : BitEncoding α) :
    FP (nonemptyEncoding e) BitEncoding.bits
      (fun xs : NonemptyList α => BitEncoding.frames (xs.val.map e.encode)) :=
  (ListCodecMachines.fp_payload e).transportInput Subtype.val (fun _ => rfl)

/-- The first item and remaining framed payload are literally a typed product word. -/
theorem fp_split (e : BitEncoding α) (d : α) :
    FP (nonemptyEncoding e) (e.prod BitEncoding.bits)
      (fun xs : NonemptyList α => (xs.val.headD d, BitEncoding.frames (xs.val.tail.map e.encode))) := by
  apply (fp_payload e).transportOutput
  intro xs
  rcases xs with ⟨xs, hx⟩
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons a xs => rfl

theorem fp_head_nonempty (e : BitEncoding α) (d : α) :
    FP (nonemptyEncoding e) e (fun xs : NonemptyList α => xs.val.headD d) :=
  (fp_split e d).comp (fp_fst e BitEncoding.bits)

theorem fp_tail_nonempty (e : BitEncoding α) (d : α) :
    FP (nonemptyEncoding e) e.list (fun xs : NonemptyList α => xs.val.tail) := by
  have hl : FP (nonemptyEncoding e) BitEncoding.nat (fun xs : NonemptyList α => xs.val.length) :=
    (ListCodecMachines.fp_length e).transportInput Subtype.val (fun _ => rfl)
  have hn := (hl.pair (fp_const (nonemptyEncoding e) BitEncoding.nat 1)).comp fp_subtraction
  have ht := (fp_split e d).comp (fp_snd e BitEncoding.bits)
  apply (hn.pair ht).transportOutput
  intro xs
  simp only [Function.comp_apply, BitEncoding.prod, BitEncoding.bits, BitEncoding.list, List.length_tail, id_eq]

/-- Total list head with an explicit fixed default, using exact canonical item codes. -/
theorem fp_headD (e : BitEncoding α) (d : α) :
    FP e.list e (fun xs : List α => xs.headD d) := by
  apply ((fp_prepare e d).comp (fp_head_nonempty e d)).congr
  intro xs
  cases xs <;> simp [prepare, ensureNonempty]

/-- Total list tail, including an empty input and strict machine cleanup. -/
theorem fp_tail (e : BitEncoding α) (d : α) : FP e.list e.list (List.tail : List α → List α) := by
  apply ((fp_prepare e d).comp (fp_tail_nonempty e d)).congr
  intro xs
  cases xs <;> simp [prepare, ensureNonempty]

end
end PlanarHom.ListDecompositionMachines
