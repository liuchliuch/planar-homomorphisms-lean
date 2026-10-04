import PlanarHom.PlanarityLRLoopAdjacency

/-! NEW loop-port noninterleaving against every other actual occurrence in the
same computed component. No LR or alignment hypothesis is required. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints

 theorem rootRowStart_host (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (root : Fin g.vertices) (hne : directRow g bits root.val≠[]) :
    dartHost g (rootRowStart g hg bits root hne)=root.val :=
   ((mem_directRow g hg bits root.isLt _).mp
     (List.mem_of_head? (rootRowStart_head g hg bits root hne))).2

 theorem rootRowStart_isRootFirst (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (root : Fin g.vertices) (hz : PlanarityDepthFirstSearch.height g root.val=0)
    (hne : directRow g bits root.val≠[]) : RootFirst g bits (eraseDart (rootRowStart g hg bits root hne)) := by
  have hh:PlanarityRotationCode.host g (eraseDart (rootRowStart g hg bits root hne))=root.val:=rootRowStart_host g hg bits root hne
  exact ⟨by simpa only [hh] using hz,by simpa only [hh] using rootRowStart_head g hg bits root hne⟩

 theorem componentStart_isRootFirst (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (a : Dart (Fin g.edges.length)) : RootFirst g bits (eraseDart (componentContourStart g hg bits a)) :=
   rootRowStart_isRootFirst g hg bits _ (componentRoot_spec g (dartHost_valid g hg a)).2.2 _

 theorem componentStart_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (a : Dart (Fin g.edges.length)) :
    componentRoot g (dartHost g (componentContourStart g hg bits a))=componentRoot g (dartHost g a) := by
  unfold componentContourStart
  rw [rootRowStart_host]
  exact componentRoot_eq_self g (componentRoot_spec g (dartHost_valid g hg a)).1
    (componentRoot_spec g (dartHost_valid g hg a)).2.2

 theorem contourKey_index_strict (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (a : Dart (Fin g.edges.length)) (hs : RootFirst g bits (eraseDart a))
    (i j : ℕ) (hij : i<j) (hj : j<Function.minimalPeriod (dfsContour g hg bits) a) :
    contourKey g bits (eraseDart ((dfsContour g hg bits)^[i] a))<
      contourKey g bits (eraseDart ((dfsContour g hg bits)^[j] a)) := by
  have hi:i<Function.minimalPeriod (dfsContour g hg bits) a:=hij.trans hj
  have h:=List.pairwise_iff_getElem.mp (dfsContourWord_key_sorted g hg bits a hs) i j
    (by simpa only [dfsContourWord,List.length_map,List.length_range] using hi)
    (by simpa only [dfsContourWord,List.length_map,List.length_range] using hj) hij
  simpa only [dfsContourWord,List.getElem_map,List.getElem_range] using h

 theorem loop_outward_eq (g : MixedCode) {e : ℕ} (hl : (edge g e).1=(edge g e).2.1) :
    PlanarityRotationCode.outward g e=(e,true) := by
  have hs:source g e=(edge g e).1 := by
    rcases PlanarityRotationCode.source_target_endpoints g e with h | h
    · exact congrArg Prod.fst h
    · exact (congrArg Prod.fst h).trans hl.symm
  simp [PlanarityRotationCode.outward,hs]

 theorem loop_port_key_noncrossing (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e f : ℕ} (he : e<g.edges.length) (hf : f<g.edges.length)
    (hl : (edge g e).1=(edge g e).2.1) (hne : e≠f)
    (hr : componentRoot g (source g e)=componentRoot g (source g f)) :
    PortNoncrossing
      (contourKey g bits (PlanarityRotationCode.outward g e))
      (contourKey g bits (PlanarityRotationCode.reverse (PlanarityRotationCode.outward g e)))
      (contourKey g bits (PlanarityRotationCode.outward g f))
      (contourKey g bits (PlanarityRotationCode.reverse (PlanarityRotationCode.outward g f))) := by
  let x:=typedOutward g ⟨e,he⟩
  let y:=reversePerm _ x
  let u:=typedOutward g ⟨f,hf⟩
  let v:=reversePerm _ u
  let s:=componentContourStart g hg bits x
  let P:=dfsContour g hg bits
  let key:=fun a:Dart (Fin g.edges.length)=>contourKey g bits (eraseDart a)
  have hs:RootFirst g bits (eraseDart s):=componentStart_isRootFirst g hg bits x
  have hstrict:∀i j,i<j→j<Function.minimalPeriod P s→key (P^[i] s)<key (P^[j] s):=
    contourKey_index_strict g hg bits s hs
  have hroot:componentRoot g (dartHost g s)=componentRoot g (source g e):=by
    simpa only [s,x,dartHost_typedOutward] using componentStart_componentRoot g hg bits x
  have hx:P.SameCycle s x := (dfsContour_sameCycle_iff_componentRoot_eq g hg bits s x).mpr
    (by simpa only [x,dartHost_typedOutward] using hroot)
  have hu:P.SameCycle s u := (dfsContour_sameCycle_iff_componentRoot_eq g hg bits s u).mpr
    (by simpa only [u,dartHost_typedOutward] using hroot.trans hr)
  have hv:P.SameCycle s v := (dfsContour_sameCycle_iff_componentRoot_eq g hg bits s v).mpr
    (by simpa only [v,u,dartHost_reverse_typedOutward] using (hroot.trans hr).trans (source_target_componentRoot g hg hf))
  have hnext:P x=y := by
    apply eraseDart_injective g
    simp only [P,y,dfsContour_erase,erase_reversePerm,x,erase_typedOutward,loop_outward_eq g hl]
    exact loop_contour_successor g hg bits he hl
  have hxy:key x<key y := by
    simpa only [key,x,y,erase_reversePerm,erase_typedOutward,loop_outward_eq g hl,
      PlanarityRotationCode.reverse,Bool.not_true] using loop_key_lt g hg bits he hl
  have hux:u≠x := fun h=>hne (congrArg (fun a:Dart (Fin g.edges.length)=>a.1.val) h).symm
  have huy:u≠y := fun h=>hne (congrArg (fun a:Dart (Fin g.edges.length)=>a.1.val) h).symm
  have hvx:v≠x := fun h=>hne (congrArg (fun a:Dart (Fin g.edges.length)=>a.1.val) h).symm
  have hvy:v≠y := fun h=>hne (congrArg (fun a:Dart (Fin g.edges.length)=>a.1.val) h).symm
  have hnon:=OrderedCycleAdjacentPorts.noncrossing_of_outside hxy
    (OrderedCycleAdjacentPorts.outside_adjacent P s key hstrict hx hu hnext hxy hux huy)
    (OrderedCycleAdjacentPorts.outside_adjacent P s key hstrict hx hv hnext hxy hvx hvy)
  simpa only [key,x,y,u,v,erase_reversePerm,erase_typedOutward] using hnon

end PlanarHom.PlanarityLRRealization
