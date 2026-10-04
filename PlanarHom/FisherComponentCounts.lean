import PlanarHom.FisherRotationConnected

/-! NEW exact component-quotient bijections for occurrence relabeling,
path/endloop expansion and polygon/triangle replacement. Isolated original
vertices remain separate components of the expansion. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
open Kasteleyn PlanarityLRRealization
variable {V E W F : Type*} [Fintype E] [Fintype F]
variable {G : MultiGraph V E} {H : MultiGraph W F}

 theorem component_map_of_edges (f : V→W)
    (hf : ∀e,H.componentSetoid Finset.univ (f (G.src e)) (f (G.dst e)))
    {u v : V} (h : G.componentSetoid Finset.univ u v) :
    H.componentSetoid Finset.univ (f u) (f v) := by
  let color:V→H.Components Finset.univ:=fun v=>Quotient.mk _ (f v)
  exact Quotient.exact (G.edgeConstant_respects Finset.univ color (fun e _=>Quotient.sound (hf e)) h)

 def componentEquivOfProjection (p : V→W) (hp : Function.Surjective p)
    (hconn : ∀u v,G.componentSetoid Finset.univ u v ↔ H.componentSetoid Finset.univ (p u) (p v)) :
    G.Components Finset.univ ≃ H.Components Finset.univ :=
  Equiv.ofBijective (Quotient.map p (fun _ _ h=>(hconn _ _).mp h)) (by
    constructor
    · intro x y
      induction x using Quotient.inductionOn with | _ u =>
        induction y using Quotient.inductionOn with | _ v =>
          intro h
          exact Quotient.sound ((hconn u v).mpr (Quotient.exact h))
    · intro x
      induction x using Quotient.inductionOn with | _ v =>
        obtain ⟨u,rfl⟩:=hp v
        exact ⟨Quotient.mk _ u,rfl⟩)

 def DartRelabel.symm (e : DartRelabel G H) : DartRelabel H G where
  vertex:=e.vertex.symm
  dart:=e.dart.symm
  reverse a:=by
    apply e.dart.injective
    rw [e.dart.apply_symm_apply,e.reverse,e.dart.apply_symm_apply]
  host a:=by
    apply e.vertex.injective
    rw [←e.host,e.dart.apply_symm_apply,e.vertex.apply_symm_apply]

 theorem DartRelabel.component_map (e : DartRelabel G H) {u v : V}
    (h : G.componentSetoid Finset.univ u v) :
    H.componentSetoid Finset.univ (e.vertex u) (e.vertex v) := by
  apply component_map_of_edges e.vertex ?_ h
  intro f
  have hh:=H.dart_hosts_connected (e.dart (f,true))
  rw [←e.reverse,e.host,e.host] at hh
  exact hh

 theorem DartRelabel.component_iff (e : DartRelabel G H) (u v : V) :
    G.componentSetoid Finset.univ u v ↔ H.componentSetoid Finset.univ (e.vertex u) (e.vertex v) := by
  constructor
  · exact e.component_map
  · intro h
    have hh:=e.symm.component_map h
    simpa only [DartRelabel.symm,e.vertex.symm_apply_apply] using hh

 theorem DartRelabel.componentCount [Fintype V] [Fintype W] (e : DartRelabel G H) :
    H.componentCount Finset.univ=G.componentCount Finset.univ :=
  (Fintype.card_congr (componentEquivOfProjection e.vertex e.vertex.surjective e.component_iff)).symm

end PlanarHom.MultiGraph

namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}

 theorem expansion_component_iff (o : G.IncidenceOrdering) (u v : ExpansionVertex o) :
    (expansionGraph o).componentSetoid Finset.univ u v ↔ G.componentSetoid Finset.univ u.1 v.1 := by
  constructor
  · apply component_map_of_edges Sigma.fst
    intro e
    cases e with
    | inl e =>
      have he:G.componentSetoid Finset.univ (G.src e) (G.dst e):=Relation.EqvGen.rel _ _ ⟨e,Finset.mem_univ _,rfl,rfl⟩
      simpa only [expansionGraph,Sum.elim_inl,portVertex,IncidenceOrdering.darts_symm_vertex,dartVertex,
        Bool.false_eq_true,if_false,if_true] using he
    | inr e => exact .refl _
  · intro h
    have hh:=component_map_of_edges (G:=G) (H:=expansionGraph o)
      (fun v=>(⟨v,0⟩:ExpansionVertex o)) (expansion_anchors_edge o) h
    exact Relation.EqvGen.trans _ _ _ (expansion_anchor_connected o u.1 u.2).symm
      (Relation.EqvGen.trans _ _ _ hh (expansion_anchor_connected o v.1 v.2))

 theorem expansion_componentCount (o : G.IncidenceOrdering) :
    (expansionGraph o).componentCount Finset.univ=G.componentCount Finset.univ :=
  Fintype.card_congr (componentEquivOfProjection (G:=expansionGraph o) (H:=G) Sigma.fst
    (fun v=>⟨⟨v,0⟩,rfl⟩) (expansion_component_iff o))

variable [DecidableEq (Dart E)] (R : RotationRows G)

 theorem polygon_component_iff (hinc : ∀v,∃a : Dart E,(G.dartPair a).1=v) (a b : Dart E) :
    (polygonGraph R).componentSetoid Finset.univ a b ↔
      G.componentSetoid Finset.univ (G.dartPair a).1 (G.dartPair b).1 := by
  constructor
  · apply component_map_of_edges (fun a=>(G.dartPair a).1)
    intro e
    cases e with
    | inl e => exact Relation.EqvGen.rel _ _ ⟨e,Finset.mem_univ _,rfl,rfl⟩
    | inr a =>
      change G.componentSetoid Finset.univ (G.dartPair a).1 (G.dartPair (R.rotation a)).1
      rw [R.rotation_host]
  · intro h
    let anchor:V→Dart E:=fun v=>Classical.choose (hinc v)
    have ha:∀v,(G.dartPair (anchor v)).1=v:=fun v=>Classical.choose_spec (hinc v)
    have hedge (e:E) : (polygonGraph R).componentSetoid Finset.univ (anchor (G.src e)) (anchor (G.dst e)) := by
      have hs:=polygon_same_host_connected R (anchor (G.src e)) (e,true) (ha _)
      have ht:=polygon_same_host_connected R (e,false) (anchor (G.dst e)) (ha _).symm
      have he:(polygonGraph R).componentSetoid Finset.univ (e,true) (e,false):=
        Relation.EqvGen.rel _ _ ⟨.inl e,Finset.mem_univ _,rfl,rfl⟩
      exact Relation.EqvGen.trans _ _ _ hs (Relation.EqvGen.trans _ _ _ he ht)
    have hh:=component_map_of_edges anchor hedge h
    exact Relation.EqvGen.trans _ _ _ (polygon_same_host_connected R a _ (ha _).symm)
      (Relation.EqvGen.trans _ _ _ hh (polygon_same_host_connected R _ b (ha _)))

 theorem polygon_componentCount (hinc : ∀v,∃a : Dart E,(G.dartPair a).1=v) :
    (polygonGraph R).componentCount Finset.univ=G.componentCount Finset.univ :=
  Fintype.card_congr (componentEquivOfProjection (G:=polygonGraph R) (H:=G) (fun a=>(G.dartPair a).1)
    hinc (polygon_component_iff R hinc))

 theorem cubic_componentCount (p : (V×Fin 3)≃(E×Bool)) (R : RotationRows (cubicOriginal p)) :
    (cubicDecoration p).componentCount Finset.univ=(cubicOriginal p).componentCount Finset.univ :=
  (cubicRelabel p R).componentCount.trans (polygon_componentCount R (cubicOriginal_incident p))

end PlanarHom.Fisher
