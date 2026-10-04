import PlanarHom.RootedOccurrenceTreeCuts

/-! NEW concrete occurrence-index child lookup and exact root incidence for a
valid finite recursive occurrence tree. No geometric assumption is used. -/
namespace PlanarHom.MultiGraph.RootedOccurrenceTree
variable {V E : Type*} {G : MultiGraph V E}

def childPairs : RootedOccurrenceTree V E → List (E×RootedOccurrenceTree V E)
  | .node _ cs => cs

def childLookup [DecidableEq E] (t : RootedOccurrenceTree V E) (e : E) : Option (RootedOccurrenceTree V E) :=
  t.childPairs.lookup e

theorem child_edges_nodup {v : V} {cs : List (E×RootedOccurrenceTree V E)}
    (ht : (node v cs).Valid G) : (cs.map Prod.fst).Nodup := by
  apply List.pairwise_map.mpr
  apply (child_vertices_disjoint ht).imp_of_mem
  intro c d hc hd hdis hEq
  have heq:c.2.root=d.2.root:=
    ((compatible_node _ _).mp ht.1 c hc).2.1.symm.trans
      ((congrArg G.dst hEq).trans ((compatible_node _ _).mp ht.1 d hd).2.1)
  exact hdis c.2.root_mem_vertices (heq ▸ d.2.root_mem_vertices)

theorem child_unique {v : V} {cs : List (E×RootedOccurrenceTree V E)}
    (ht : (node v cs).Valid G) {c d : E×RootedOccurrenceTree V E}
    (hc : c∈cs) (hd : d∈cs) (he : c.1=d.1) : c=d :=
  List.inj_on_of_nodup_map (child_edges_nodup ht) hc hd he

private theorem lookup_iff_mem [DecidableEq E] {T : Type*} (xs : List (E×T))
    (hn : (xs.map Prod.fst).Nodup) (e : E) (t : T) : xs.lookup e=some t ↔ (e,t)∈xs := by
  constructor
  · intro h
    obtain ⟨pre,post,hparts,_⟩:=List.lookup_eq_some_iff.mp h
    rw [hparts]
    simp
  · intro h
    obtain ⟨pre,post,hparts⟩:=List.mem_iff_append.mp h
    subst xs
    apply List.lookup_eq_some_iff.mpr
    refine ⟨pre,post,rfl,?_⟩
    have hd := (List.nodup_append.mp (show (pre.map Prod.fst++e::post.map Prod.fst).Nodup by
      simpa only [List.map_append,List.map_cons] using hn)).2.2
    intro p hp
    have hne:e≠p.1 := by
      intro he
      exact hd e (List.mem_map.mpr ⟨p,hp,he.symm⟩) e (by simp) rfl
    simp [bne,Bool.beq_eq_decide_eq,hne]

theorem childLookup_eq_some_iff [DecidableEq E] (t : RootedOccurrenceTree V E) (ht : t.Valid G)
    (e : E) (u : RootedOccurrenceTree V E) : t.childLookup e=some u ↔ (e,u)∈t.childPairs := by
  cases t with
  | node v cs => exact lookup_iff_mem cs (child_edges_nodup ht) e u

theorem childLookup_eq_none_iff [DecidableEq E] (t : RootedOccurrenceTree V E) (ht : t.Valid G)
    (e : E) : t.childLookup e=none ↔ ∀u,(e,u)∉t.childPairs := by
  constructor
  · intro hn u hu
    have hh:=(childLookup_eq_some_iff t ht e u).mpr hu
    rw [hn] at hh
    contradiction
  · intro hn
    cases h:t.childLookup e with
    | none => rfl
    | some u => exact (hn u ((childLookup_eq_some_iff t ht e u).mp h)).elim

theorem dst_ne_root (t : RootedOccurrenceTree V E) (ht : t.Valid G) {e : E} (he : e∈t.edges) :
    G.dst e≠t.root := by
  cases t with
  | node v cs =>
    rw [edges_node] at he
    obtain ⟨c,hc,he⟩:=List.mem_flatMap.mp he
    rcases List.mem_cons.mp he with rfl | he
    · intro h
      have hs:=((compatible_node _ _).mp ht.1 c hc).1
      exact child_nonloop ht c hc (hs.trans h.symm)
    · exact (child_edges_nonincident_root ht c hc e he).2

theorem src_root_iff_child (t : RootedOccurrenceTree V E) (ht : t.Valid G) (e : E) :
    e∈t.edges ∧ G.src e=t.root ↔ ∃u,(e,u)∈t.childPairs := by
  cases t with
  | node v cs =>
    constructor
    · rintro ⟨he,hs⟩
      rw [edges_node] at he
      obtain ⟨c,hc,he⟩:=List.mem_flatMap.mp he
      rcases List.mem_cons.mp he with he | he
      · exact ⟨c.2,by simpa only [he,Prod.mk.eta] using hc⟩
      · exact ((child_edges_nonincident_root ht c hc e he).1 hs).elim
    · rintro ⟨u,hu⟩
      rw [edges_node]
      exact ⟨List.mem_flatMap.mpr ⟨(e,u),hu,List.mem_cons_self ..⟩,
        ((compatible_node _ _).mp ht.1 (e,u) hu).1⟩

theorem incident_tree_dart_iff_lookup [DecidableEq E] (t : RootedOccurrenceTree V E) (ht : t.Valid G)
    (a : Kasteleyn.Dart E) :
    a.1∈t.edges ∧ (G.dartPair a).1=t.root ↔ ∃u,t.childLookup a.1=some u ∧ a.2=true := by
  rcases a with ⟨e,b⟩
  cases b with
  | false =>
    simp only [dartPair,Bool.false_eq_true,if_false,Prod.fst,and_false,exists_false,iff_false,not_and]
    exact fun he=>dst_ne_root t ht he
  | true =>
    simpa [dartPair] using (src_root_iff_child t ht e).trans
      (exists_congr (fun u=>(childLookup_eq_some_iff t ht e u).symm))

end PlanarHom.MultiGraph.RootedOccurrenceTree
