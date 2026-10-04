import PlanarHom.PortPatchAssembly
import PlanarHom.PlanarityLRRealizationRotationSystem

/-! NEW literal reverse-patch concatenation of local rotation rows. The finite
vertex scan is explicit, so this construction has an executable fixed-table form. -/
noncomputable section
open Classical
namespace PlanarHom.PortPatchAssembly
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {C B : Type} {P W E : C → Type}
variable (G : ∀c,MultiGraph (P c ⊕ W c) (E c)) (port : ∀c,P c→B)
variable [∀c,DecidableEq (Dart (E c))] [DecidableEq (Dart (Sigma E))]
variable (rows : ∀c,RotationRows (G c))
variable (vertices : ∀c,List (P c ⊕ W c))
variable (hv : ∀c,(vertices c).Nodup) (hcover : ∀c w,w∈vertices c)

def localRowWord (c : C) (v : Vertex (B:=B) (W:=W)) : List (Dart (E c)) :=
  (vertices c).flatMap (fun w=>if placeVertex port c w=v then (rows c).row w else [])

 include hcover in
 theorem localRowWord_mem (c : C) (v : Vertex (B:=B) (W:=W)) (a : Dart (E c)) :
     a∈localRowWord G port rows vertices c v ↔ placeVertex port c ((G c).dartPair a).1=v := by
   simp only [localRowWord,List.mem_flatMap]
   constructor
   · rintro ⟨w,_,ha⟩
     split_ifs at ha with hw
     · rw [(rows c).mem w a |>.mp ha]
       exact hw
     · simp at ha
   · intro ha
     refine ⟨((G c).dartPair a).1,hcover c _,?_⟩
     simp only [ha,if_pos]
     exact ((rows c).mem _ a).mpr rfl

 include hv in
 theorem localRowWord_nodup (c : C) (v : Vertex (B:=B) (W:=W)) :
     (localRowWord G port rows vertices c v).Nodup := by
   apply List.nodup_flatMap.mpr
   constructor
   · intro w _
     split_ifs
     · exact (rows c).nodup w
     · exact List.nodup_nil
   · apply (hv c).imp
     intro w z hn
     apply List.disjoint_left.mpr
     intro a ha hb
     dsimp only at ha hb
     split_ifs at ha hb with hw hz
     · exact hn (((rows c).mem w a).mp ha |>.symm.trans (((rows c).mem z a).mp hb))
     all_goals simp_all

 def liftPatchDart (c : C) (a : Dart (E c)) : Dart (Sigma E) := (⟨c,a.1⟩,a.2)

 theorem liftPatchDart_injective (c : C) : Function.Injective (liftPatchDart (E:=E) c) := by
   rintro ⟨e,b⟩ ⟨f,d⟩ h
   have he : e=f := by simpa only [liftPatchDart,Prod.mk.injEq,Sigma.mk.inj_iff,heq_eq_eq,true_and] using congrArg Prod.fst h
   exact Prod.ext he (congrArg (fun a:Dart (Sigma E)=>a.2) h)

 theorem liftPatchDart_host (c : C) (a : Dart (E c)) :
     ((graph G port).dartPair (liftPatchDart c a)).1=placeVertex port c ((G c).dartPair a).1 := by
   rcases a with ⟨e,b⟩
   cases b <;> rfl

 def rowWord (order : List C) (v : Vertex (B:=B) (W:=W)) : List (Dart (Sigma E)) :=
   order.flatMap (fun c=>(localRowWord G port rows vertices c v).map (liftPatchDart c))

 include hv in
 theorem rowWord_nodup (order : List C) (ho:order.Nodup) (v : Vertex (B:=B) (W:=W)) :
     (rowWord G port rows vertices order v).Nodup := by
   apply List.nodup_flatMap.mpr
   constructor
   · intro c _
     exact (localRowWord_nodup G port rows vertices hv c v).map (liftPatchDart_injective c)
   · apply ho.imp
     intro c d hn
     apply List.disjoint_left.mpr
     intro a ha hb
     obtain ⟨x,_,hx⟩:=List.mem_map.mp ha
     obtain ⟨y,_,hy⟩:=List.mem_map.mp hb
     exact hn (congrArg (fun a:Dart (Sigma E)=>a.1.1) (hx.trans hy.symm))

 include hcover in
 theorem rowWord_mem (order : List C) (horder:∀c,c∈order)
     (v : Vertex (B:=B) (W:=W)) (a : Dart (Sigma E)) :
     a∈rowWord G port rows vertices order v ↔ ((graph G port).dartPair a).1=v := by
   simp only [rowWord,List.mem_flatMap,List.mem_map]
   constructor
   · rintro ⟨c,_,b,hb,rfl⟩
     rw [liftPatchDart_host]
     exact (localRowWord_mem G port rows vertices hcover c v b).mp hb
   · rcases a with ⟨⟨c,e⟩,b⟩
     intro ha
     refine ⟨c,horder c,(e,b),?_,rfl⟩
     apply (localRowWord_mem G port rows vertices hcover c v (e,b)).mpr
     exact (liftPatchDart_host G port c (e,b)) ▸ ha

 def rotationRows (order : List C) (ho:order.Nodup) (horder:∀c,c∈order) :
     RotationRows (graph G port) where
   row := rowWord G port rows vertices order
   nodup := rowWord_nodup G port rows vertices hv order ho
   mem := rowWord_mem G port rows vertices hcover order horder

end PlanarHom.PortPatchAssembly
