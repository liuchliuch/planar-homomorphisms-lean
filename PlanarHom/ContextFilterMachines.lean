import PlanarHom.ListContextMachines
import PlanarHom.ListFilterMachines

/-! Actual filtering with a materialized input-dependent context. -/
namespace PlanarHom.ContextFilterMachines
open PlanarHom.Complexity

private theorem tag_filter {C α : Type} (c : C) (p : C×α→Bool) (xs : List α) :
    ((xs.map (fun a=>(c,a))).filter p).map Prod.snd=xs.filter (fun a=>p (c,a)):=by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>cases hp:p (c,a) <;> simp [hp,ih]

theorem fp_filterWithContext {C α : Type} (ec : BitEncoding C) (ea : BitEncoding α)
    (p : C×α→Bool) (hp : FP (ec.prod ea) BitEncoding.bool p) :
    FP (ec.prod ea.list) ea.list (fun q=>q.2.filter (fun a=>p (q.1,a))):=by
  have ht:=PlanarHom.ListContextMachines.fp_mapWithContext ec ea (ec.prod ea) id (fp_id _)
  have hf:=ht.comp (PlanarHom.ListFilterMachines.fp_filter (ec.prod ea) p hp)
  have hl:=hf.comp (PlanarHom.ListMapMachines.fp_map (ec.prod ea) ea Prod.snd
    (PairProjectionMachines.fp_snd ec ea))
  exact hl.congr (fun q=>tag_filter q.1 p q.2)

end PlanarHom.ContextFilterMachines
