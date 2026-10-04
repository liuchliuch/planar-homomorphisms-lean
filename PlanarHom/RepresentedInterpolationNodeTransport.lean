import PlanarHom.RepresentedPowerTableNodes
import PlanarHom.LagrangeRecovery

noncomputable section
open Classical
namespace PlanarHom.RepresentedPowerTable
open RepresentedBit
variable {K:Type} [Field K] (P:Presentation K) {t:ℕ}

theorem map_get_cast {C D:Type} (xs:List C) (f:C→D) (ys:List D) (h:xs.map f=ys)
    (hl:xs.length=ys.length) (i:Fin xs.length) : f (xs.get i)=ys.get (Fin.cast hl i) := by
  have he:=congrArg (fun l:List D=>l[i.val]?) h
  simpa only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,
    List.getElem?_eq_getElem (by omega: i.val<ys.length),Option.map_some,Option.some.injEq,List.get_eq_getElem] using he

theorem evaluateReplacement_cast {n m:ℕ} (h:n=m) (μ θ y:Fin n→K) :
    LagrangeRecovery.evaluateReplacement μ θ y=
      LagrangeRecovery.evaluateReplacement (fun i=>μ (Fin.cast h.symm i))
        (fun i=>θ (Fin.cast h.symm i)) (fun i=>y (Fin.cast h.symm i)) := by
  subst m
  rfl

theorem evaluateReplacement_table (rs:List (Row P t)) (ss:List (K×K))
    (hs:rs.map (fun r=>(source P r,target P r))=ss) (f:ℕ→K) :
    LagrangeRecovery.evaluateReplacement (sourceNode P rs) (targetNode P rs) (fun i=>f i.val)=
      LagrangeRecovery.evaluateReplacement (fun i:Fin ss.length=>(ss.get i).1)
        (fun i:Fin ss.length=>(ss.get i).2) (fun i=>f i.val) := by
  have hl:rs.length=ss.length:=by simpa only [List.length_map] using congrArg List.length hs
  rw [evaluateReplacement_cast hl]
  congr 1
  · funext i
    have he:=map_get_cast rs _ ss hs hl (Fin.cast hl.symm i)
    exact congrArg Prod.fst he
  · funext i
    have he:=map_get_cast rs _ ss hs hl (Fin.cast hl.symm i)
    exact congrArg Prod.snd he

end PlanarHom.RepresentedPowerTable
