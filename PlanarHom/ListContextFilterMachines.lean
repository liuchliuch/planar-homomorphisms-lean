import PlanarHom.ListContextMachines
import PlanarHom.ListFilterMachines

/-! Actual typed filtering with a retained shared context. -/
namespace PlanarHom.ListContextFilterMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
variable {C α : Type}

theorem map_filter_pairs (p : C×α→Bool) (c : C) (xs : List α) :
    (((xs.map (fun a => (c,a))).filter p).map Prod.snd)=xs.filter (fun a => p (c,a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : p (c,a) <;> simp [h,ih]

/-- Materialize context/value pairs, run the actual typed filter, then project
retained original values. No context-dependent predicate is treated as free. -/
theorem fp_filterWithContext (ec : BitEncoding C) (ea : BitEncoding α) (p : C×α→Bool)
    (hp : FP (ec.prod ea) BitEncoding.bool p) :
    FP (ec.prod ea.list) ea.list (fun q => q.2.filter (fun a => p (q.1,a))) := by
  have hm := ListContextMachines.fp_mapWithContext ec ea (ec.prod ea) id (fp_id (ec.prod ea))
  have hf := ListFilterMachines.fp_filter (ec.prod ea) p hp
  have hd := ListMapMachines.fp_map (ec.prod ea) ea Prod.snd (fp_snd ec ea)
  exact ((hm.comp hf).comp hd).congr (fun q => map_filter_pairs p q.1 q.2)

end PlanarHom.ListContextFilterMachines
