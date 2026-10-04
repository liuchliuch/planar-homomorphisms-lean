import PlanarHom.ListContextMachines
import PlanarHom.ListPredicateMachines

/-! Actual finite all-pairs tests with one preserved ordinary context. -/
namespace PlanarHom.ContextPairTestMachines
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
variable {C R : Type} (ec : BitEncoding C) (er : BitEncoding R)

def anyPair (bad : C → R → R → Bool) (p : C × List R) : Bool :=
  p.2.any (fun a => p.2.any (fun b => bad p.1 a b))

theorem fp_anyPair (bad : C → R → R → Bool)
    (hb : FP ((ec.prod er).prod er) BitEncoding.bool (fun p => bad p.1.1 p.1.2 p.2)) :
    FP (ec.prod er.list) BitEncoding.bool (anyPair bad) := by
  have hi := (ListContextMachines.fp_mapWithContext (ec.prod er) er BitEncoding.bool _ hb).comp
    (ListPredicateMachines.fp_any BitEncoding.bool id (fp_id BitEncoding.bool))
  have hp := fp_fst (ec.prod er.list) er
  have hc := hp.comp (fp_fst ec er.list)
  have hl := hp.comp (fp_snd ec er.list)
  have ha := fp_snd (ec.prod er.list) er
  have hbody := ((hc.pair ha).pair hl).comp hi
  have ho := (ListContextMachines.fp_mapWithContext (ec.prod er.list) er BitEncoding.bool _ hbody).comp
    (ListPredicateMachines.fp_any BitEncoding.bool id (fp_id BitEncoding.bool))
  exact (((fp_id (ec.prod er.list)).pair (fp_snd ec er.list)).comp ho).congr
    (fun p => by simp [anyPair,List.any_map])

theorem anyPair_eq_false_iff (bad : C → R → R → Bool) (p : C × List R) :
    anyPair bad p = false ↔ ∀ a ∈ p.2, ∀ b ∈ p.2, bad p.1 a b = false := by
  simp [anyPair, List.any_eq_false]

end PlanarHom.ContextPairTestMachines
