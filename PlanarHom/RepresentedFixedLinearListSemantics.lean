import PlanarHom.RepresentedFixedLinearArithmetic
import Mathlib.Data.List.OfFn

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RepresentedBit
variable {K:Type} [CommSemiring K]

theorem AddMulMachines.dot_list {P:Presentation K} (ops:AddMulMachines P) (k:ℕ)
    (c:Fin k→K) (bs:List P.Code) (hv:∀b∈bs,P.valid b) (y:Fin k→K)
    (hy:bs.map P.value=List.ofFn y) :
    P.valid (ops.dot k (fun i=>P.constant (c i)) bs) ∧
      P.value (ops.dot k (fun i=>P.constant (c i)) bs)=∑i,c i*y i := by
  have hl:bs.length=k:=by simpa only [List.length_map,List.length_ofFn] using congrArg List.length hy
  have he:∃zs:Fin k→P.Code,bs=List.ofFn zs:=by
    subst k
    exact ⟨bs.get,(List.ofFn_get bs).symm⟩
  obtain ⟨zs,rfl⟩:=he
  have hvalue:∀i,P.value (zs i)=y i:=by
    intro i
    have hh:=congrArg (fun l=>l[i.val]?) hy
    simpa only [List.map_ofFn,List.getElem?_ofFn,i.isLt,dif_pos,Option.some.injEq,Function.comp_apply,Fin.eta] using hh
  have h:=ops.dot_ofFn k (fun i=>P.constant (c i)) zs (fun i=>P.constant_valid _)
    (fun i=>hv _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  refine ⟨h.1,?_⟩
  simpa only [P.constant_value,hvalue] using h.2

end PlanarHom.RepresentedBit
