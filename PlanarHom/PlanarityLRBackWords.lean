import PlanarHom.PlanarityLRTreeWords

/-! NEW prefix-free event words for actual back occurrences within a DFS
component. Terminal back-edge ranks cannot be confused with tree descent. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints

 theorem desc_eq_of_height_eq (g : MixedCode) {u v : ℕ} (hv : v<g.vertices)
    (hd : Desc g u v) (hh : height g u=height g v) : u=v := by
  rcases hd with he | ha
  · exact he
  · have hs:=ancestors_height_lt g hv ha
    omega

 theorem exists_child_toward (g : MixedCode) {u v : ℕ} (hv : v<g.vertices)
    (huv : u∈ancestors g v) :
    ∃w, w<g.vertices ∧ parentVertex g w=u ∧ Desc g w v ∧ height g w=height g u+1 := by
  have hh:=ancestors_height_lt g hv huv
  let w:=(rootPath g v).getD (height g u+1) v
  have hm:=rootPath_getD_mem g v (height g u+1) (by omega)
  have hd : Desc g w v:=rootPath_mem_desc g hm
  have hw:w<g.vertices:=desc_valid g hv hd
  have hh' : height g w=height g u+1:=rootPath_getD_height g hv (by omega)
  have hp:0<height g w:=by omega
  have hpar:=parentVertex_ancestor g hw hp
  have hpv:=desc_trans g hv (Or.inr hpar) hd
  have hph:=parent_height g hw hp
  have heh:height g (parentVertex g w)=height g u:=by omega
  have hu:=ancestors_valid g hv huv
  have hpeq:parentVertex g w=u := by
    rcases desc_comparable g hv hpv (Or.inr huv) with h | h
    · exact desc_eq_of_height_eq g hu h heh
    · exact (desc_eq_of_height_eq g (ancestors_valid g hw hpar) h heh.symm).symm
  exact ⟨w,hw,hpeq,hd,hh'⟩

 theorem backEdge_mem_orderedOutgoing (g : MixedCode) (bits : List Bool) {b : ℕ}
    (hb : isBack g b=true) : b∈orderedOutgoing g bits (source g b) := by
  rw [mem_orderedOutgoing]
  simp [outgoing,(of_decide_eq_true hb).1,hb]

@[simp] theorem backWord_length (g : MixedCode) (bits : List Bool) (b : ℕ) :
    (backWord g bits b).length=height g (source g b)+1 := by simp [backWord]

 theorem backWord_prefix_free (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {b c : ℕ} (hb : isBack g b=true) (hc : isBack g c=true)
    (hr : componentRoot g (source g b)=componentRoot g (source g c))
    (hp : (backWord g bits b).IsPrefix (backWord g bits c)) : b=c := by
  have hub:source g b<g.vertices:=(source_target_valid g hg (of_decide_eq_true hb).1).1
  have hvc:source g c<g.vertices:=(source_target_valid g hg (of_decide_eq_true hc).1).1
  have hlen:height g (source g b)≤height g (source g c) := by
    have hh:=hp.length_le
    simp only [backWord_length] at hh
    omega
  have hbc : (treeWord g bits (source g b)).IsPrefix (backWord g bits c) :=
    (List.prefix_append _ _).trans hp
  have hcc : (treeWord g bits (source g c)).IsPrefix (backWord g bits c) := List.prefix_append _ _
  have htrees : (treeWord g bits (source g b)).IsPrefix (treeWord g bits (source g c)) :=
    List.prefix_of_prefix_length_le hbc hcc (by simpa only [treeWord_length] using hlen)
  have hdesc:=(treeWord_prefix_iff_desc g hg bits hub hvc hr).mp htrees
  rcases hdesc with hs | ha
  · have hw:=hp.eq_of_length (by simp only [backWord_length,hs])
    have hi:(orderedOutgoing g bits (source g c)).idxOf b=(orderedOutgoing g bits (source g c)).idxOf c := by
      simpa only [backWord,hs,List.append_right_inj,List.singleton_inj] using hw
    apply (List.idxOf_inj (l := orderedOutgoing g bits (source g c))
      (by simpa only [hs] using backEdge_mem_orderedOutgoing g bits hb)
      (backEdge_mem_orderedOutgoing g bits hc)).mp hi
  · obtain ⟨w,hw,hpw,hwv,hwh⟩:=exists_child_toward g hvc ha
    have hwpos:0<height g w:=by omega
    have hpw' : (treeWord g bits w).IsPrefix (backWord g bits c) :=
      (treeWord_prefix_of_desc g bits hvc hwv).trans hcc
    have heql:(backWord g bits b).length=(treeWord g bits w).length := by
      simp only [backWord_length,treeWord_length,hwh]
    have hpw'' : (backWord g bits b).IsPrefix (treeWord g bits w) :=
      List.prefix_of_prefix_length_le hp hpw' heql.le
    have heq:=hpw''.eq_of_length heql
    rw [treeWord_parent g bits hw hwpos,hpw] at heq
    have hi:(orderedOutgoing g bits (source g b)).idxOf b=
        (orderedOutgoing g bits (source g b)).idxOf (parentEdge g w) := by
      simpa only [backWord,List.append_right_inj,List.singleton_inj] using heq
    have hmem:parentEdge g w∈orderedOutgoing g bits (source g b) := by
      simpa only [hpw] using parentEdge_mem_orderedOutgoing g hg bits hw hwpos
    have hedge:b=parentEdge g w:=
      (List.idxOf_inj (backEdge_mem_orderedOutgoing g bits hb) hmem).mp hi
    have ht:=(parentEdge_tree g hg hw hwpos).1
    have hf:=(of_decide_eq_true hb).2.1
    rw [hedge,ht] at hf
    contradiction

 theorem backWord_injective (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {b c : ℕ} (hb : isBack g b=true) (hc : isBack g c=true)
    (hr : componentRoot g (source g b)=componentRoot g (source g c))
    (he : backWord g bits b=backWord g bits c) : b=c :=
   backWord_prefix_free g hg bits hb hc hr (by rw [he])

end PlanarHom.PlanarityLRDirect
