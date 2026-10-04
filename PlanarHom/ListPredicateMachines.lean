import PlanarHom.ListContextMachines
import PlanarHom.ConditionalMachines

/-! # Actual finite Boolean accumulation and typed relational membership -/
namespace PlanarHom.ListPredicateMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines

variable {α : Type}

theorem fold_or_eq_any (p : α→Bool) (b : Bool) (xs : List α) :
    xs.foldl (fun acc a => acc || p a) b = (b || xs.any p) := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih => simp [ih,Bool.or_assoc]

/-- Polynomial-time existential testing over a dynamically sized typed list. -/
theorem fp_any (e : BitEncoding α) (p : α→Bool) (hp : FP e BitEncoding.bool p) :
    FP e.list BitEncoding.bool (fun xs => xs.any p) := by
  have hleft := fp_fst BitEncoding.bool e
  have hright := (fp_snd BitEncoding.bool e).comp hp
  have hbody := (hleft.pair hright).comp (fp_bool_gate (fun q => q.1 || q.2))
  have hfold := ListFoldMachines.fp_foldl e BitEncoding.bool (fun acc a => acc || p a) hbody 1
    (fun b xs i _ => by simp [BitEncoding.bool])
  exact (((fp_const e.list BitEncoding.bool false).pair (fp_id e.list)).comp hfold).congr
    (fun xs => by simp [fold_or_eq_any])

/-- Membership for any computable binary Boolean relation, with the candidate
as shared context. Equality is not assumed at the machine layer. -/
theorem fp_member (e : BitEncoding α) (test : α×α→Bool)
    (htest : FP (e.prod e) BitEncoding.bool test) :
    FP (e.prod e.list) BitEncoding.bool (fun p => p.2.any (fun a => test (p.1,a))) := by
  have hm := ListContextMachines.fp_mapWithContext e e BitEncoding.bool test htest
  exact (hm.comp (fp_any BitEncoding.bool id (fp_id BitEncoding.bool))).congr
    (fun p => by simp [List.any_map])

end PlanarHom.ListPredicateMachines
