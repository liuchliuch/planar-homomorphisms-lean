import PlanarHom.FisherExpansionRotation
import PlanarHom.RotationFaceCycleDuality

/-! NEW complete literal face transitions of the degree-reduction path and
its two endpoint loops. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E} (o : G.IncidenceOrdering)

 theorem expansion_cycle_zero (v : V) :
    (expansionRows o).rotation (expansionPathDart o v 0 true)=expansionLoopDart o v false true ∧
    (expansionRows o).rotation (expansionLoopDart o v false true)=expansionLoopDart o v false false ∧
    (expansionRows o).rotation (expansionLoopDart o v false false)=expansionPathDart o v 0 true :=
  (expansionRows o).rotation_of_three ⟨v,0⟩ _ _ _ (expansionRow_zero o v)

 theorem expansion_cycle_last (v : V) :
    (expansionRows o).rotation (expansionPathDart o v (Fin.last (o.degree v)) false)=expansionLoopDart o v true true ∧
    (expansionRows o).rotation (expansionLoopDart o v true true)=expansionLoopDart o v true false ∧
    (expansionRows o).rotation (expansionLoopDart o v true false)=expansionPathDart o v (Fin.last (o.degree v)) false :=
  (expansionRows o).rotation_of_three ⟨v,Fin.last (o.degree v+1)⟩ _ _ _ (expansionRow_last o v)

 theorem expansion_cycle_port (v : V) (i : Fin (o.degree v)) :
    (expansionRows o).rotation (expansionPathDart o v i.castSucc false)=expansionPortDart o v i ∧
    (expansionRows o).rotation (expansionPortDart o v i)=expansionPathDart o v i.succ true ∧
    (expansionRows o).rotation (expansionPathDart o v i.succ true)=expansionPathDart o v i.castSucc false :=
  (expansionRows o).rotation_of_three ⟨v,i.succ.castSucc⟩ _ _ _ (expansionRow_port o v i)

 theorem expansion_face_path_forward (v : V) (i : Fin (o.degree v)) :
    (expansionRows o).facePerm (expansionPathDart o v i.castSucc true)=expansionPortDart o v i :=
  (expansion_cycle_port o v i).1

 theorem expansion_face_path_backward (v : V) (i : Fin (o.degree v)) :
    (expansionRows o).facePerm (expansionPathDart o v i.succ false)=expansionPathDart o v i.castSucc false :=
  (expansion_cycle_port o v i).2.2

 theorem expansion_face_port (v : V) (i : Fin (o.degree v)) :
    (expansionRows o).facePerm (reversePerm _ (expansionPortDart o v i))=expansionPathDart o v i.succ true := by
  change (expansionRows o).rotation (reversePerm _ (reversePerm _ (expansionPortDart o v i)))=_
  rw [show reversePerm _ (reversePerm _ (expansionPortDart o v i))=expansionPortDart o v i from
    (reversePerm _).symm_apply_apply _]
  exact (expansion_cycle_port o v i).2.1

 theorem expansion_face_path_zero (v : V) :
    (expansionRows o).facePerm (expansionPathDart o v 0 false)=expansionLoopDart o v false true :=
  (expansion_cycle_zero o v).1

 theorem expansion_face_path_last (v : V) :
    (expansionRows o).facePerm (expansionPathDart o v (Fin.last (o.degree v)) true)=expansionLoopDart o v true true :=
  (expansion_cycle_last o v).1

 theorem expansion_face_loop_false (v : V) (b : Bool) :
    (expansionRows o).facePerm (expansionLoopDart o v b false)=expansionLoopDart o v b false := by
  cases b
  · exact (expansion_cycle_zero o v).2.1
  · exact (expansion_cycle_last o v).2.1

 theorem expansion_face_loop_zero (v : V) :
    (expansionRows o).facePerm (expansionLoopDart o v false true)=expansionPathDart o v 0 true :=
  (expansion_cycle_zero o v).2.2

 theorem expansion_face_loop_last (v : V) :
    (expansionRows o).facePerm (expansionLoopDart o v true true)=expansionPathDart o v (Fin.last (o.degree v)) false :=
  (expansion_cycle_last o v).2.2

end PlanarHom.Fisher
