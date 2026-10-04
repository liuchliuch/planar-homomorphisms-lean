import PlanarHom.PlanarityDepthFirstSearchProgram

/-! NEW reconstruction. Honest nested-list DFS codecs and concrete machine
views/assemblers; there is no free conversion of dynamic records. -/
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity PairProjectionMachines

 def arcCode : BitEncoding Arc := BitEncoding.nat.prod BitEncoding.nat
 def edgeCode : BitEncoding Edge := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)
 def taskParts (t : Task) := (t.enter,(t.vertex,(t.edge,t.path)))
 def discoveryParts (d : Discovery) := (d.vertex,(d.treeEdge,d.ancestors))
 def stateParts (s : State) := (s.work,(s.active,(s.discovered,s.finished)))

 def taskPartsCode := BitEncoding.bool.prod (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat.list))
 def taskCode : BitEncoding Task := taskPartsCode.retract taskParts
   (fun p=>⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩) (by intro t; cases t; rfl)
 def discoveryPartsCode := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat.list)
 def discoveryCode : BitEncoding Discovery := discoveryPartsCode.retract discoveryParts
   (fun p=>⟨p.1,p.2.1,p.2.2⟩) (by intro t; cases t; rfl)
 def statePartsCode := taskCode.list.prod
   (BitEncoding.nat.list.prod (discoveryCode.list.prod BitEncoding.nat.list))
 def stateCode : BitEncoding State := statePartsCode.retract stateParts
   (fun p=>⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩) (by intro s; cases s; rfl)

 theorem fp_taskParts : FP taskCode taskPartsCode taskParts := fp_code_view _ _ _ (fun _=>rfl)
 theorem fp_discoveryParts : FP discoveryCode discoveryPartsCode discoveryParts := fp_code_view _ _ _ (fun _=>rfl)
 theorem fp_stateParts : FP stateCode statePartsCode stateParts := fp_code_view _ _ _ (fun _=>rfl)

 theorem fp_enter : FP taskCode BitEncoding.bool Task.enter :=
  fp_taskParts.comp (fp_fst _ _)
 theorem fp_vertex : FP taskCode BitEncoding.nat Task.vertex :=
  (fp_taskParts.comp (fp_snd _ _)).comp (fp_fst _ _)
 theorem fp_edge : FP taskCode BitEncoding.nat Task.edge :=
  ((fp_taskParts.comp (fp_snd _ _)).comp (fp_snd _ _)).comp (fp_fst _ _)
 theorem fp_path : FP taskCode BitEncoding.nat.list Task.path :=
  ((fp_taskParts.comp (fp_snd _ _)).comp (fp_snd _ _)).comp (fp_snd _ _)
 theorem fp_discoveredVertex : FP discoveryCode BitEncoding.nat Discovery.vertex :=
  fp_discoveryParts.comp (fp_fst _ _)
 theorem fp_treeEdge : FP discoveryCode BitEncoding.nat Discovery.treeEdge :=
  (fp_discoveryParts.comp (fp_snd _ _)).comp (fp_fst _ _)
 theorem fp_ancestors : FP discoveryCode BitEncoding.nat.list Discovery.ancestors :=
  (fp_discoveryParts.comp (fp_snd _ _)).comp (fp_snd _ _)
 theorem fp_work : FP stateCode taskCode.list State.work :=
  fp_stateParts.comp (fp_fst _ _)
 theorem fp_active : FP stateCode BitEncoding.nat.list State.active :=
  (fp_stateParts.comp (fp_snd _ _)).comp (fp_fst _ _)
 theorem fp_discovered : FP stateCode discoveryCode.list State.discovered :=
  ((fp_stateParts.comp (fp_snd _ _)).comp (fp_snd _ _)).comp (fp_fst _ _)
 theorem fp_finished : FP stateCode BitEncoding.nat.list State.finished :=
  ((fp_stateParts.comp (fp_snd _ _)).comp (fp_snd _ _)).comp (fp_snd _ _)
 theorem fp_seen : FP stateCode BitEncoding.nat.list seen :=
  fp_discovered.comp (ListMapMachines.fp_map discoveryCode BitEncoding.nat Discovery.vertex fp_discoveredVertex)

 theorem fp_mkTask {A : Type} (ea : BitEncoding A) (b : A→Bool) (v e : A→ℕ) (p : A→List ℕ)
    (hb : FP ea BitEncoding.bool b) (hv : FP ea BitEncoding.nat v) (he : FP ea BitEncoding.nat e)
    (hp : FP ea BitEncoding.nat.list p) : FP ea taskCode (fun a=>⟨b a,v a,e a,p a⟩) :=
  (hb.pair (hv.pair (he.pair hp))).transportOutput (fun _=>rfl)

 theorem fp_mkDiscovery {A : Type} (ea : BitEncoding A) (v e : A→ℕ) (p : A→List ℕ)
    (hv : FP ea BitEncoding.nat v) (he : FP ea BitEncoding.nat e) (hp : FP ea BitEncoding.nat.list p) :
    FP ea discoveryCode (fun a=>⟨v a,e a,p a⟩) :=
  (hv.pair (he.pair hp)).transportOutput (fun _=>rfl)

 theorem fp_mkState {A : Type} (ea : BitEncoding A) (w : A→List Task) (a : A→List ℕ)
    (d : A→List Discovery) (f : A→List ℕ)
    (hw : FP ea taskCode.list w) (ha : FP ea BitEncoding.nat.list a)
    (hd : FP ea discoveryCode.list d) (hf : FP ea BitEncoding.nat.list f) :
    FP ea stateCode (fun x=>⟨w x,a x,d x,f x⟩) :=
  (hw.pair (ha.pair (hd.pair hf))).transportOutput (fun _=>rfl)

 theorem fp_exitTask : FP BitEncoding.nat taskCode exitTask :=
  fp_mkTask _ _ _ _ _ (fp_const _ _ false) (fp_id _) (fp_const _ _ 0) (fp_const _ _ [])

end PlanarHom.PlanarityDepthFirstSearch
