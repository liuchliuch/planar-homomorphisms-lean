import PlanarHom.PlanarityLRContourTraversalOrder
import PlanarHom.PlanarityLRVisitWordRelabel

/-! NEW exact linear event order of the actual contour, starting at the first
dart of its actual root row. This is a list equality, not only a permutation. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints

 theorem contourBackEvents_sorted (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) (hstart : RootFirst g bits (eraseDart a)) :
    (contourBackEvents g hg bits a).Pairwise (fun e f=>eventLE g bits e f=true) := by
  apply (contourBackEvents_key_sorted g hg bits a hstart).imp_of_mem
  intro e f he hf hkey
  have hse:=(mem_contourBackEvents g hg bits a e).mp he
  have hsf:=(mem_contourBackEvents g hg bits a f).mp hf
  apply (eventLE_iff g bits e f).mpr
  exact Or.inl ((contourKey_outward_lt_iff g hg bits hse.1 hsf.1 (hse.2.trans hsf.2.symm)).mp hkey)

 theorem contourBackEvents_eq_componentBackEvents (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) (hstart : RootFirst g bits (eraseDart a)) :
    contourBackEvents g hg bits a=componentBackEvents g bits (componentRoot g (dartHost g a)) := by
  let r : ℕ→ℕ→Prop:=fun e f=>eventLE g bits e f=true
  letI : IsAntisymm ℕ r:=⟨eventLE_antisymm g bits⟩
  exact List.eq_of_perm_of_sorted (r := r) (contourBackEvents_perm g hg bits a)
    (contourBackEvents_sorted g hg bits a hstart) ((backEvents_sorted g bits).filter _)

 theorem contourOutwardBackDarts_eq (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) (hstart : RootFirst g bits (eraseDart a)) :
    (((contourPortWord (directRotationRows g hg bits) (fun e=>isTree g e.val) a).filter
      (outwardBackFlag g)).map eraseDart)=
      (componentBackEvents g bits (componentRoot g (dartHost g a))).map (PlanarityRotationCode.outward g) := by
  rw [← contourBackEvents_eq_componentBackEvents g hg bits a hstart,contourBackEvents,List.map_map]
  apply List.map_congr_left
  intro b hb
  have hh : isBack g b.1.val=true ∧ b=typedOutward g b.1 := by
    simpa only [outwardBackFlag,Bool.and_eq_true,decide_eq_true_eq] using (List.mem_filter.mp hb).2
  change eraseDart b=PlanarityRotationCode.outward g b.1.val
  conv_lhs => rw [hh.2]
  exact erase_typedOutward g b.1

 theorem contourBackEvents_eq_from_root_row (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (root : Fin g.vertices) (hz : PlanarityDepthFirstSearch.height g root.val=0)
    (a : Dart (Fin g.edges.length)) (hfirst : (directRow g bits root.val).head?=some (eraseDart a)) :
    contourBackEvents g hg bits a=componentBackEvents g bits root.val := by
  have hm : eraseDart a∈directRow g bits root.val := by
    cases hrow:directRow g bits root.val with
    | nil => simp [hrow] at hfirst
    | cons b bs =>
      have he:b=eraseDart a:=by simpa [hrow] using hfirst
      simp [hrow,he]
  have hhost:PlanarityRotationCode.host g (eraseDart a)=root.val:=
    ((mem_directRow g hg bits root.isLt (eraseDart a)).mp hm).2
  have hstart : RootFirst g bits (eraseDart a):=⟨by simpa only [hhost] using hz,by simpa only [hhost] using hfirst⟩
  rw [contourBackEvents_eq_componentBackEvents g hg bits a hstart]
  simp only [dartHost,hhost,componentRoot_eq_self g root.isLt hz]

 def rootRowStart (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (root : Fin g.vertices) (hne : directRow g bits root.val≠[]) : Dart (Fin g.edges.length) :=
   liftDart ((directRow g bits root.val).head hne)
     (((mem_directRow g hg bits root.isLt _).mp (List.head_mem hne)).1)

 theorem rootRowStart_head (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (root : Fin g.vertices) (hne : directRow g bits root.val≠[]) :
    (directRow g bits root.val).head?=some (eraseDart (rootRowStart g hg bits root hne)) := by
  simp only [rootRowStart,erase_liftDart,List.head?_eq_head hne]

 theorem contourBackEvents_rootRowStart (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (root : Fin g.vertices) (hz : PlanarityDepthFirstSearch.height g root.val=0)
    (hne : directRow g bits root.val≠[]) :
    contourBackEvents g hg bits (rootRowStart g hg bits root hne)=componentBackEvents g bits root.val :=
   contourBackEvents_eq_from_root_row g hg bits root hz _ (rootRowStart_head g hg bits root hne)

 theorem componentRoot_row_ne_nil (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    directRow g bits (componentRoot g (dartHost g a))≠[] := by
  obtain ⟨b,hb,_⟩:=dfsContourForRows_to_componentRoot g hg (directRotationRows g hg bits) a
  have hr:=(componentRoot_spec g (dartHost_valid g hg a)).1
  have hm:eraseDart b∈directRow g bits (componentRoot g (dartHost g a)):=
    (mem_directRow g hg bits hr _).mpr ⟨b.1.isLt,hb⟩
  intro he
  simp only [he,List.not_mem_nil] at hm

 def componentContourStart (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (a : Dart (Fin g.edges.length)) : Dart (Fin g.edges.length) :=
   rootRowStart g hg bits
     ⟨componentRoot g (dartHost g a),(componentRoot_spec g (dartHost_valid g hg a)).1⟩
     (componentRoot_row_ne_nil g hg bits a)

 theorem contourBackEvents_componentStart (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    contourBackEvents g hg bits (componentContourStart g hg bits a)=
      componentBackEvents g bits (componentRoot g (dartHost g a)) :=
   contourBackEvents_rootRowStart g hg bits _ (componentRoot_spec g (dartHost_valid g hg a)).2.2 _

end PlanarHom.PlanarityLRRealization
