import PlanarHom.PortPatchRotationRows

/-! NEW order transport through the literal local-vertex scan and patch-row
concatenation. The relation is arbitrary; geometric clockwise inequalities can
be supplied for each local row and between successive patch blocks. -/
noncomputable section
open Classical
namespace PlanarHom.PortPatchAssembly
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {C B : Type} {P W E : C→Type}
variable (G:∀c,MultiGraph (P c⊕W c) (E c)) (port:∀c,P c→B)
variable [∀c,DecidableEq (Dart (E c))] [DecidableEq (Dart (Sigma E))]
variable (rows:∀c,RotationRows (G c)) (vertices:∀c,List (P c⊕W c))
variable (R:Dart (Sigma E)→Dart (Sigma E)→Prop)

 theorem localRowWord_pairwise (c:C) (v:Vertex (B:=B) (W:=W))
    (hv:(vertices c).Nodup) (hinj:Function.Injective (placeVertex (W:=W) port c))
    (hlocal:∀w∈vertices c,((rows c).row w |>.map (liftPatchDart c)).Pairwise R) :
    ((localRowWord G port rows vertices c v).map (liftPatchDart c)).Pairwise R := by
  apply List.pairwise_map.mpr
  apply List.pairwise_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro w hw
    split_ifs
    · exact List.pairwise_map.mp (hlocal w hw)
    · exact List.Pairwise.nil
  · apply hv.imp
    intro w z hne a ha b hb
    split_ifs at ha hb with hw hz
    · exact (hne (hinj (hw.trans hz.symm))).elim
    all_goals simp_all

 theorem rowWord_pairwise (order:List C) (v:Vertex (B:=B) (W:=W))
    (hv:∀c,(vertices c).Nodup) (hinj:∀c,Function.Injective (placeVertex (W:=W) port c))
    (hlocal:∀c∈order,∀w∈vertices c,((rows c).row w |>.map (liftPatchDart c)).Pairwise R)
    (hcross:order.Pairwise (fun c d=>∀a∈localRowWord G port rows vertices c v,
      ∀b∈localRowWord G port rows vertices d v,R (liftPatchDart c a) (liftPatchDart d b))) :
    (rowWord G port rows vertices order v).Pairwise R := by
  apply List.pairwise_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro c hc
    exact localRowWord_pairwise G port rows vertices R c v (hv c) (hinj c) (hlocal c hc)
  · apply hcross.imp
    intro c d h a ha b hb
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hb
    exact h x hx y hy

 theorem rotationRows_pairwise (hv:∀c,(vertices c).Nodup) (hcover:∀c w,w∈vertices c)
    (order:List C) (ho:order.Nodup) (horder:∀c,c∈order) (v:Vertex (B:=B) (W:=W))
    (hinj:∀c,Function.Injective (placeVertex (W:=W) port c))
    (hlocal:∀c∈order,∀w∈vertices c,((rows c).row w |>.map (liftPatchDart c)).Pairwise R)
    (hcross:order.Pairwise (fun c d=>∀a∈localRowWord G port rows vertices c v,
      ∀b∈localRowWord G port rows vertices d v,R (liftPatchDart c a) (liftPatchDart d b))) :
    ((rotationRows G port rows vertices hv hcover order ho horder).row v).Pairwise R :=
  rowWord_pairwise G port rows vertices R order v hv hinj hlocal hcross

end PlanarHom.PortPatchAssembly
