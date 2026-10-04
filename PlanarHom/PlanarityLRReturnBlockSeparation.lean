import PlanarHom.PlanarityLRDirectedNodeExpansion
import PlanarHom.ListBlockSeparation
import PlanarHom.PlanarityLRDirectedSubtreeRanks

/-! NEW uniform order of all returns from distinct outgoing DFS branches. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityDepthFirstSearch

theorem outgoing_ne_parent (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (parent e : Fin g.edges.length) (hp : isTree g parent.val=true)
    (he : e.val∈outgoing g (target g parent.val)) : e≠parent := by
  intro h
  have hs := (outgoing_spec g he).2.2
  rw [h] at hs
  have hh := tree_height_succ g hg hp
  rw [hs] at hh
  omega

theorem return_mem_directedNodeBlock (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (parent e b : Fin g.edges.length)
    (hp : isTree g parent.val=true) (he : e.val∈outgoing g (target g parent.val))
    (hb : b.val∈returns g e.val) :
    (b,true)∈directedNodeBlock g hg rows parent (e,true) := by
  rw [directedNodeBlock,if_neg (outgoing_ne_parent g hg parent e hp he)]
  by_cases ht : isTree g e.val=true
  · rw [if_pos ht,mem_directedSubtreePorts g hg rows e ht,directedSubtreeKeep_eq_true g hg]
    have hh := (returns_tree_iff g ht b.val).mp hb
    exact ⟨(of_decide_eq_true hh.1).2.1,hh.2.1⟩
  · rw [if_neg ht]
    have hb' : b=e := by
      unfold returns at hb
      rw [if_neg ht] at hb
      split_ifs at hb with hbback
      · exact Fin.ext (by simpa only [List.mem_singleton] using hb)
      · simp only [List.not_mem_nil] at hb
    simp only [hb',List.mem_singleton]

theorem returns_uniform_sublist_order (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (parent e f : Fin g.edges.length)
    (hp : isTree g parent.val=true)
    (he : e.val∈outgoing g (target g parent.val)) (hf : f.val∈outgoing g (target g parent.val))
    (hne : e≠f) :
    (∀ b c : Fin g.edges.length, b.val∈returns g e.val → c.val∈returns g f.val →
      [(b,true),(c,true)].Sublist (directedSubtreePorts g hg rows parent)) ∨
    (∀ b c : Fin g.edges.length, b.val∈returns g e.val → c.val∈returns g f.val →
      [(c,true),(b,true)].Sublist (directedSubtreePorts g hg rows parent)) := by
  let row := rows.row (dfsTarget g hg parent)
  have hpar : (parent,false)∈row := (rows.mem _ _).mpr rfl
  have hehost : ((dfsGraph g hg).dartPair (e,true)).1=dfsTarget g hg parent :=
    Fin.ext (outgoing_spec g he).2.2
  have hfhost : ((dfsGraph g hg).dartPair (f,true)).1=dfsTarget g hg parent :=
    Fin.ext (outgoing_spec g hf).2.2
  have hea : (e,true)∈afterParentRow row (parent,false) :=
    (mem_afterParentRow row _ (rows.nodup _) hpar _).mpr
      ⟨(rows.mem _ _).mpr hehost,by intro h; have := congrArg Prod.snd h; cases this⟩
  have hfa : (f,true)∈afterParentRow row (parent,false) :=
    (mem_afterParentRow row _ (rows.nodup _) hpar _).mpr
      ⟨(rows.mem _ _).mpr hfhost,by intro h; have := congrArg Prod.snd h; cases this⟩
  have hne' : (e,true)≠(f,true) := fun h => hne (congrArg Prod.fst h)
  have hw : directedSubtreePorts g hg rows parent=
      (afterParentRow row (parent,false)).flatMap (directedNodeBlock g hg rows parent) := by
    rw [directedSubtreePorts_eq_afterParent g hg rows parent hp,afterParentInputs_eq_flatMap]
  rcases uniform_block_sublist_order (afterParentRow row (parent,false))
    (directedNodeBlock g hg rows parent) hea hfa hne' with h | h
  · exact Or.inl (fun b c hb hc => hw ▸ h (b,true)
      (return_mem_directedNodeBlock g hg rows parent e b hp he hb) (c,true)
      (return_mem_directedNodeBlock g hg rows parent f c hp hf hc))
  · exact Or.inr (fun b c hb hc => hw ▸ h (b,true)
      (return_mem_directedNodeBlock g hg rows parent e b hp he hb) (c,true)
      (return_mem_directedNodeBlock g hg rows parent f c hp hf hc))

theorem returns_uniform_root_sublist_order (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r v : Fin g.vertices)
    (hr : height g r.val=0) (hv : 0 < height g v.val) (hroot : componentRoot g v.val=r.val)
    (e f : Fin g.edges.length) (he : e.val∈outgoing g v.val) (hf : f.val∈outgoing g v.val)
    (hne : e≠f) :
    (∀ b c : Fin g.edges.length, b.val∈returns g e.val → c.val∈returns g f.val →
      [(b,true),(c,true)].Sublist (directedRootPorts g hg rows r)) ∨
    (∀ b c : Fin g.edges.length, b.val∈returns g e.val → c.val∈returns g f.val →
      [(c,true),(b,true)].Sublist (directedRootPorts g hg rows r)) := by
  let parent : Fin g.edges.length := ⟨parentEdge g v.val,parentEdge_lt g v.isLt hv⟩
  have hp := parentEdge_tree g hg v.isLt hv
  have hpr : componentRoot g (source g parent.val)=r.val := by
    rw [tree_componentRoot g hg hp.1,hp.2.1]
    exact hroot
  have hs := (directedSubtreePorts_infix_root g hg rows r hr parent hp.1 hpr).sublist
  have he' : e.val∈outgoing g (target g parent.val) := by simpa only [parent,hp.2.1] using he
  have hf' : f.val∈outgoing g (target g parent.val) := by simpa only [parent,hp.2.1] using hf
  rcases returns_uniform_sublist_order g hg rows parent e f hp.1 he' hf' hne with h | h
  · exact Or.inl (fun b c hb hc => (h b c hb hc).trans hs)
  · exact Or.inr (fun b c hb hc => (h b c hb hc).trans hs)

theorem returns_uniform_root_rank_order (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r v : Fin g.vertices)
    (hr : height g r.val=0) (hv : 0 < height g v.val) (hroot : componentRoot g v.val=r.val)
    (e f : Fin g.edges.length) (he : e.val∈outgoing g v.val) (hf : f.val∈outgoing g v.val)
    (hne : e≠f) :
    (∀ b c : Fin g.edges.length, b.val∈returns g e.val → c.val∈returns g f.val →
      (directedRootPorts g hg rows r).idxOf (b,true)<(directedRootPorts g hg rows r).idxOf (c,true)) ∨
    (∀ b c : Fin g.edges.length, b.val∈returns g e.val → c.val∈returns g f.val →
      (directedRootPorts g hg rows r).idxOf (c,true)<(directedRootPorts g hg rows r).idxOf (b,true)) := by
  have hn := directedRootPorts_nodup g hg rows r
  rcases returns_uniform_root_sublist_order g hg rows r v hr hv hroot e f he hf hne with h | h
  · exact Or.inl (fun b c hb hc => by
      simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using idxOf_lt_of_pair_sublist _ hn (h b c hb hc))
  · exact Or.inr (fun b c hb hc => by
      simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using idxOf_lt_of_pair_sublist _ hn (h b c hb hc))

end PlanarHom.PlanarityLRRealization
