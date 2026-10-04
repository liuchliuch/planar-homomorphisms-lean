import PlanarHom.PlanarityLRBlockRankOrder

/-! NEW separation of entire actual contour branch blocks, including every
dart hosted in a tree-child subtree. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityRotationCode

 theorem visitTreeWord_prefix_of_desc (g : MixedCode) (bits : List Bool) {u v : ℕ}
    (hv : v<g.vertices) (hd : Desc g u v) :
    (visitTreeWord g bits u).IsPrefix (visitTreeWord g bits v) :=
   (((rootPath_prefix_iff_desc g hv).mpr hd).drop 1).map _

 theorem child_contourKey_decompose (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e : ℕ} (he : isTree g e=true) {a : Dart} (ha : a.1<g.edges.length)
    (hd : Desc g (target g e) (host g a)) :
    ∃tail, contourKey g bits a=visitTreeWord g bits (source g e)++
      localRank g bits (source g e) (outward g e)::tail := by
  have hp : (visitTreeWord g bits (target g e)).IsPrefix (contourKey g bits a) :=
    (visitTreeWord_prefix_of_desc g bits (host_valid g hg ha) hd).trans (List.prefix_append _ _)
  obtain ⟨tail,heq⟩:=hp
  rw [visitTreeWord_tree_target g hg bits he] at heq
  exact ⟨tail,by simpa only [List.append_assoc,List.singleton_append] using heq.symm⟩

 def InContourBranch (g : MixedCode) (bits : List Bool) (e : ℕ) (a : Dart) : Prop :=
   a∈edgeBlock g bits e ∨ isTree g e=true ∧ Desc g (target g e) (host g a)

 theorem contourBranch_key_decompose (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v e : ℕ} (he : e∈orderedOutgoing g bits v)
    {a : Dart} (ha : a.1<g.edges.length) (hbranch : InContourBranch g bits e a) :
    ∃d∈edgeBlock g bits e,∃tail,contourKey g bits a=visitTreeWord g bits v++localRank g bits v d::tail := by
  have hsource:source g e=v:=(outgoing_spec g ((mem_orderedOutgoing g bits v e).mp he)).2.2
  rcases hbranch with hm | ⟨ht,hd⟩
  · have hh:=(edgeBlock_host g hg bits ((mem_orderedOutgoing g bits v e).mp he) hm).2
    exact ⟨a,hm,[],by simp only [contourKey,hh]⟩
  · obtain ⟨tail,hkey⟩:=child_contourKey_decompose g hg bits ht ha hd
    exact ⟨outward g e,by simp [edgeBlock],tail,by simpa only [hsource] using hkey⟩

 theorem branch_block_key_separation (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v e f : ℕ}
    (he : e∈orderedOutgoing g bits v) (hf : f∈orderedOutgoing g bits v)
    (hr : (orderedOutgoing g bits v).idxOf e<(orderedOutgoing g bits v).idxOf f)
    {a b : Dart} (ha : a.1<g.edges.length) (hb : b.1<g.edges.length)
    (hea : InContourBranch g bits e a) (hfb : InContourBranch g bits f b) :
    contourKey g bits a<contourKey g bits b := by
  obtain ⟨d,hd,as,hea⟩:=contourBranch_key_decompose g hg bits he ha hea
  obtain ⟨c,hc,bs,hfb⟩:=contourBranch_key_decompose g hg bits hf hb hfb
  have hs:=outgoing_spec g ((mem_orderedOutgoing g bits v e).mp he)
  have hv:v<g.vertices:=by rw [← hs.2.2]; exact (source_target_valid g hg hs.1).1
  have hi:=distinct_blocks_rank_lt g hg bits hv he hf hr hd hc
  rw [hea,hfb]
  exact List.Lex.append_left (·<·) (List.Lex.rel hi) _

end PlanarHom.PlanarityLRDirect
