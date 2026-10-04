import PlanarHom.FisherExpansionEuler

/-! NEW actual connectivity and positive degree of connected occurrence
components, including the path replacing an isolated original vertex. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable (o : G.IncidenceOrdering)

 theorem expansion_path_connected (v : V) (k : Fin (o.degree v+1)) :
    (expansionGraph o).componentSetoid Finset.univ ⟨v,k.castSucc⟩ ⟨v,k.succ⟩ :=
  Relation.EqvGen.rel _ _ ⟨.inr ⟨v,.inl k⟩,Finset.mem_univ _,rfl,rfl⟩

 theorem expansion_anchor_connected (v : V) (j : Fin (o.degree v+2)) :
    (expansionGraph o).componentSetoid Finset.univ ⟨v,0⟩ ⟨v,j⟩ := by
  obtain ⟨j,hj⟩ := j
  induction j with
  | zero => exact .refl _
  | succ j ih =>
      let k : Fin (o.degree v+1) := ⟨j,by omega⟩
      exact Relation.EqvGen.trans _ _ _ (ih (by omega)) (expansion_path_connected o v k)

 theorem expansion_anchors_edge (e : E) :
    (expansionGraph o).componentSetoid Finset.univ ⟨G.src e,0⟩ ⟨G.dst e,0⟩ := by
  let s := o.darts.symm (e,false)
  let t := o.darts.symm (e,true)
  have hs : s.1=G.src e := o.darts_symm_vertex (e,false)
  have ht : t.1=G.dst e := o.darts_symm_vertex (e,true)
  have hsc := expansion_anchor_connected o s.1 s.2.succ.castSucc
  have htc := expansion_anchor_connected o t.1 t.2.succ.castSucc
  have hsp : (⟨s.1,0⟩ : ExpansionVertex o)=⟨G.src e,0⟩ := congrArg (fun v=>(⟨v,0⟩ : ExpansionVertex o)) hs
  have htp : (⟨t.1,0⟩ : ExpansionVertex o)=⟨G.dst e,0⟩ := congrArg (fun v=>(⟨v,0⟩ : ExpansionVertex o)) ht
  rw [hsp] at hsc
  rw [htp] at htc
  have he : (expansionGraph o).componentSetoid Finset.univ (portVertex o s) (portVertex o t) :=
    Relation.EqvGen.rel _ _ ⟨.inl e,Finset.mem_univ _,rfl,rfl⟩
  exact Relation.EqvGen.trans _ _ _ hsc (Relation.EqvGen.trans _ _ _ he htc.symm)

 theorem expansion_connected (hG : ∀u v,G.componentSetoid Finset.univ u v) :
    ∀u v : ExpansionVertex o,(expansionGraph o).componentSetoid Finset.univ u v := by
  let color : V→(expansionGraph o).Components Finset.univ := fun v=>Quotient.mk _ ⟨v,0⟩
  have hc : G.EdgeConstant Finset.univ color := by
    intro e _
    exact Quotient.sound (expansion_anchors_edge o e)
  intro u v
  have hh : (expansionGraph o).componentSetoid Finset.univ ⟨u.1,0⟩ ⟨v.1,0⟩ :=
    Quotient.exact (G.edgeConstant_respects Finset.univ color hc (hG u.1 v.1))
  exact Relation.EqvGen.trans _ _ _ (expansion_anchor_connected o u.1 u.2).symm
    (Relation.EqvGen.trans _ _ _ hh (expansion_anchor_connected o v.1 v.2))

 theorem incident_of_connected [Nonempty E] (hG : ∀u v,G.componentSetoid Finset.univ u v)
    (v : V) : ∃a : Dart E,(G.dartPair a).1=v := by
  let color : V→Prop := fun v=>∃a : Dart E,(G.dartPair a).1=v
  have hc : G.EdgeConstant Finset.univ color := by
    intro e _
    exact propext (iff_of_true ⟨(e,true),rfl⟩ ⟨(e,false),rfl⟩)
  let e : E := Classical.choice inferInstance
  have h := G.edgeConstant_respects Finset.univ color hc (hG (G.src e) v)
  change color v
  rw [←h]
  exact ⟨(e,true),rfl⟩

 theorem degree_pos_of_connected [Nonempty E] (hG : ∀u v,G.componentSetoid Finset.univ u v) :
    ∀v,0<o.degree v := by
  intro v
  obtain ⟨a,ha⟩ := incident_of_connected hG v
  let b : G.VertexDarts v := ⟨reversePerm E a,by rw [dartVertex_reverse,ha]⟩
  exact Nat.zero_lt_of_lt ((o.atVertex v).symm b).isLt

 theorem vertex_card_one_of_connected [IsEmpty E] [Nonempty V]
    (hG : ∀u v,G.componentSetoid Finset.univ u v) : Fintype.card V=1 := by
  have hsub : Subsingleton V := ⟨fun u v=>G.edgeConstant_respects Finset.univ id
    (fun e _=>isEmptyElim e) (hG u v)⟩
  letI := hsub
  letI : Unique V := { default := Classical.choice inferInstance,uniq := fun _=>Subsingleton.elim _ _ }
  exact Fintype.card_unique

end PlanarHom.Fisher
