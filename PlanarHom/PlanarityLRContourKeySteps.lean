import PlanarHom.PlanarityLRContourKeys

/-! NEW concrete rank changes across actual rotation and tree-contour steps. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityRotationCode
open PlanarityLRRealization
local instance contourKeyStepsDartBEq : BEq Dart := instBEqOfDecidableEq

 theorem directRotation_valid_raw (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) : (directRotation g bits a).1<g.edges.length := by
  have h:=directRotationRows_erase g hg bits (liftDart a ha)
  rw [erase_liftDart] at h
  rw [← h]
  exact ((directRotationRows g hg bits).rotation (liftDart a ha)).1.isLt

 theorem directRotation_host_raw (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) :
    host g (directRotation g bits a)=host g a := by
  simpa only [erase_liftDart] using directRotation_host g hg bits (liftDart a ha)

 theorem localRank_last_eq_parent (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v<g.vertices) (hp : 0<height g v) {a : Dart}
    (ha : a∈visitRow g bits v) (hl : localRank g bits v a+1=(visitRow g bits v).length) :
    a=reverse (outward g (parentEdge g v)) := by
  have hr:=localRank_parent_last g hg bits hv hp
  have heq : localRank g bits v a=localRank g bits v (reverse (outward g (parentEdge g v))) := by omega
  have hparent:reverse (outward g (parentEdge g v))∈visitRow g bits v := by
    rw [visitRow_parent_last g bits hp]
    simp
  exact (List.idxOf_inj ha hparent).mp heq

 theorem rotation_wrap_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length)
    (hn : a≠reverse (outward g (parentEdge g (host g a))))
    (hl : localRank g bits (host g a) a+1=(visitRow g bits (host g a)).length) : height g (host g a)=0 := by
  by_contra hh
  have hv:=host_valid g hg ha
  exact hn (localRank_last_eq_parent g hg bits hv (by omega)
    ((mem_visitRow g hg bits hv a).mpr ⟨ha,rfl⟩) hl)

 theorem rootFirst_of_rotation_wrap (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) (hz : height g (host g a)=0)
    (hl : localRank g bits (host g a) a+1=(visitRow g bits (host g a)).length) :
    RootFirst g bits (directRotation g bits a) := by
  have hh:=directRotation_host_raw g hg bits ha
  have hv:=host_valid g hg ha
  have hm : directRotation g bits a∈visitRow g bits (host g a) :=
    (mem_visitRow g hg bits hv _).mpr ⟨directRotation_valid_raw g hg bits ha,hh⟩
  have hr:=localRank_directRotation g hg bits ha
  rw [hl,Nat.mod_self] at hr
  have hhead:=(rowIndex_eq_zero_iff _ hm).mp hr
  rw [visitRow_root g bits hz] at hhead
  exact ⟨by simpa only [hh] using hz,by simpa only [hh] using hhead⟩

 theorem contourKey_outward_tree_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e : ℕ} (he : isTree g e=true) :
    contourKey g bits (outward g e)<contourKey g bits (rawContourStep g bits (outward g e)) := by
  have hv:=(source_target_valid g hg (of_decide_eq_true he).1).2
  have hp:=tree_source_parent g hg he
  have hlast:=localRank_parent_last g hg bits hv hp.2.2
  rw [hp.2.1] at hlast
  have hrot:=localRank_directRotation g hg bits (a := reverse (outward g e)) (of_decide_eq_true he).1
  simp only [host_reverse_outward] at hrot
  rw [hlast,Nat.mod_self] at hrot
  have hhost:=rawContourStep_host_tree g hg bits (a := outward g e) (of_decide_eq_true he).1 he
  simp only [host_reverse_outward] at hhost
  have hkey : contourKey g bits (rawContourStep g bits (outward g e))=
      contourKey g bits (outward g e)++[0] := by
    unfold contourKey
    rw [hhost,host_outward,visitTreeWord_tree_target g hg bits he]
    simp only [rawContourStep,outward_index,he,if_true,hrot,List.append_assoc]
  rw [hkey]
  simpa using List.Lex.append_left (·<·) (List.Lex.nil : List.Lex (·<·) ([]:List ℕ) [0])
    (contourKey g bits (outward g e))

end PlanarHom.PlanarityLRDirect
