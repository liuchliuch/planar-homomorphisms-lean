import PlanarHom.PlanarityLRComponentGraph

/-! NEW exact restriction of arbitrary original rows and their literal face permutation. -/
noncomputable section
set_option maxHeartbeats 400000
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints

variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
variable (rows : RotationRows (g.toMultiGraph hg))

theorem row_edge_component (v : ComponentVertex g r) (a : Dart (Fin g.edges.length))
    (ha : a∈rows.row v.val) : componentRoot g (source g a.1.val)=r := by
  have hh : ((g.toMultiGraph hg).dartPair a).1=v.val := (rows.mem v.val a).mp ha
  have hc : componentRoot g ((g.toMultiGraph hg).dartPair a).1.val=r :=
    (congrArg (fun w:Fin g.vertices=>componentRoot g w.val) hh).trans v.property
  exact (original_host_componentRoot g hg a).symm.trans hc

def componentRow (v : ComponentVertex g r) : List (Dart (ComponentEdge g r)) :=
  (rows.row v.val).attach.map (fun (a : {a:Dart (Fin g.edges.length) // a∈rows.row v.val})=>
    ((⟨a.val.1,row_edge_component g hg r rows v a.val a.property⟩ : ComponentEdge g r),a.val.2))

theorem componentRow_lift (v : ComponentVertex g r) :
    (componentRow g hg r rows v).map (componentDartLift g r)=rows.row v.val := by
  simp only [componentRow,List.map_map,Function.comp_def,componentDartLift,Prod.mk.eta,List.attach_map_subtype_val]

theorem componentRow_nodup (v : ComponentVertex g r) : (componentRow g hg r rows v).Nodup := by
  apply List.Nodup.of_map (componentDartLift g r)
  rw [componentRow_lift]
  exact rows.nodup v.val

theorem mem_componentRow (v : ComponentVertex g r) (a : Dart (ComponentEdge g r)) :
    a∈componentRow g hg r rows v ↔ ((componentGraph g hg r).dartPair a).1=v := by
  have hm : a∈componentRow g hg r rows v ↔ componentDartLift g r a∈rows.row v.val := by
    rw [←componentRow_lift g hg r rows v]
    constructor
    · exact fun h=>List.mem_map.mpr ⟨a,h,rfl⟩
    · intro h
      obtain ⟨b,hb,he⟩:=List.mem_map.mp h
      exact componentDartLift_injective g r he ▸ hb
  rw [hm,rows.mem]
  constructor
  · intro h
    exact Subtype.ext ((componentDartLift_host g hg r a).trans h)
  · intro h
    exact (componentDartLift_host g hg r a).symm.trans (congrArg Subtype.val h)

def componentRows : RotationRows (componentGraph g hg r) where
  row := componentRow g hg r rows
  nodup := componentRow_nodup g hg r rows
  mem := mem_componentRow g hg r rows

theorem componentRows_rotation_lift (a : Dart (ComponentEdge g r)) :
    componentDartLift g r ((componentRows g hg r rows).rotation a)=
      rows.rotation (componentDartLift g r a) := by
  have h:=map_formPerm_apply (componentDartLift g r) (componentDartLift_injective g r)
    ((componentRows g hg r rows).row ((componentGraph g hg r).dartPair a).1)
    ((componentRows g hg r rows).nodup _) ((componentRows g hg r rows).mem _ a |>.mpr rfl)
  change ((componentRow g hg r rows ((componentGraph g hg r).dartPair a).1).map
      (componentDartLift g r)).formPerm (componentDartLift g r a)=_ at h
  rw [componentRow_lift,componentDartLift_host] at h
  exact h.symm

def componentFace : Equiv.Perm (Dart (ComponentEdge g r)) :=
  (componentRows g hg r rows).rotation * reversePerm (ComponentEdge g r)

theorem componentFace_lift (a : Dart (ComponentEdge g r)) :
    componentDartLift g r (componentFace g hg r rows a)=
      (rows.rotation * reversePerm (Fin g.edges.length)) (componentDartLift g r a) := by
  simp only [componentFace,Equiv.Perm.mul_apply,componentRows_rotation_lift,componentDartLift_reverse]

end PlanarHom.PlanarityLRRealization
