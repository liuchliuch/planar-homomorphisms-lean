import PlanarHom.PalettedSignalComponents
import PlanarHom.PalettedPatchConnected

/-! NEW exact component count of the literal shared-port coloring graph.
The generated signal quotient is identified with actual graph connectivity;
private macro vertices create no additional component. -/
noncomputable section
open Classical
namespace PlanarHom.PalettedColoringPatches
open MultiGraph ThreeColorPaletteCounting
variable {C S : Type} {P W E : C→Type} [Fintype C] [∀c,Fintype (E c)] [∀c,Nonempty (P c)]
variable (L : ∀c,Patch (P c) (W c) (E c)) (signal : ∀c,P c→S)
variable (cover : ∀s,∃c,∃p:P c,signal c p=s)
variable (existsColoring : ∀c,Nonempty (Coloring (L c).graph))

 def rootPort (c : C) : P c := Classical.choice inferInstance
 def projectSignal : (S×Fin 3)⊕Sigma W→S :=
  Sum.elim Prod.fst (fun w=>signal w.1 (rootPort (P:=P) w.1))
 def signalAnchor (s : S) : (S×Fin 3)⊕Sigma W := .inl (s,2)

 theorem project_place (c : C) (v : (P c×Fin 3)⊕W c) :
    signalComponent signal (projectSignal signal (PortPatchAssembly.placeVertex (placePort signal) c v))=
      signalComponent signal (signal c (rootPort (P:=P) c)) := by
  cases v with
  | inl p => exact component_ports signal c p.1 _
  | inr w => rfl

 include existsColoring in
 theorem placed_connected (c : C) (u v : (P c×Fin 3)⊕W c) :
    (graph L signal).componentSetoid Finset.univ
      (PortPatchAssembly.placeVertex (placePort signal) c u)
      (PortPatchAssembly.placeVertex (placePort signal) c v) := by
  let color:((P c×Fin 3)⊕W c)→(graph L signal).Components Finset.univ:=
    fun v=>Quotient.mk _ (PortPatchAssembly.placeVertex (placePort signal) c v)
  have hc:(L c).graph.EdgeConstant Finset.univ color:=by
    intro e _
    exact Quotient.sound (_root_.Relation.EqvGen.rel _ _ ⟨⟨c,e⟩,Finset.mem_univ _,rfl,rfl⟩)
  exact Quotient.exact ((L c).graph.edgeConstant_respects Finset.univ color hc
    ((L c).connected (existsColoring c) u v))

 include existsColoring in
 theorem anchors_same_macro (c:C) (p q:P c) :
    (graph L signal).componentSetoid Finset.univ (signalAnchor (W:=W) (signal c p)) (signalAnchor (W:=W) (signal c q)) :=
  placed_connected L signal existsColoring c (.inl (p,2)) (.inl (q,2))

 include cover existsColoring in
 theorem vertex_anchor (v:(S×Fin 3)⊕Sigma W) :
    (graph L signal).componentSetoid Finset.univ v (signalAnchor (projectSignal signal v)) := by
  cases v with
  | inl p =>
      obtain ⟨c,q,hq⟩:=cover p.1
      have hh:=placed_connected L signal existsColoring c (.inl (q,p.2)) (.inl (q,2))
      simpa only [PortPatchAssembly.placeVertex,placePort,hq,projectSignal,Sum.elim_inl,signalAnchor] using hh
  | inr w => exact placed_connected L signal existsColoring w.1 (.inr w.2) (.inl (rootPort (P:=P) w.1,2))

 include existsColoring in
 theorem anchors_respect {s t:S} (h:signalSetoid signal s t) :
    (graph L signal).componentSetoid Finset.univ (signalAnchor (W:=W) s) (signalAnchor (W:=W) t) := by
  induction h with
  | rel s t h =>
      obtain ⟨c,p,q,rfl,rfl⟩:=h
      exact anchors_same_macro L signal existsColoring c p q
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact _root_.Relation.EqvGen.trans _ _ _ ih hj

 theorem component_project {u v:(S×Fin 3)⊕Sigma W} (h:(graph L signal).componentSetoid Finset.univ u v) :
    signalSetoid signal (projectSignal signal u) (projectSignal signal v) := by
  let color:((S×Fin 3)⊕Sigma W)→SignalComponent signal:=fun v=>signalComponent signal (projectSignal signal v)
  have hc:(graph L signal).EdgeConstant Finset.univ color:=by
    intro e _
    exact (project_place signal e.1 ((L e.1).graph.src e.2)).trans
      (project_place signal e.1 ((L e.1).graph.dst e.2)).symm
  exact Quotient.exact ((graph L signal).edgeConstant_respects Finset.univ color hc h)

 include cover existsColoring in
 theorem component_iff (u v:(S×Fin 3)⊕Sigma W) :
    (graph L signal).componentSetoid Finset.univ u v ↔
      signalSetoid signal (projectSignal signal u) (projectSignal signal v) := by
  constructor
  · exact component_project L signal
  · intro h
    exact _root_.Relation.EqvGen.trans _ _ _ (vertex_anchor L signal cover existsColoring u)
      (_root_.Relation.EqvGen.trans _ _ _ (anchors_respect L signal existsColoring h)
        (vertex_anchor L signal cover existsColoring v).symm)

 def graphComponentEquiv : (graph L signal).Components Finset.univ ≃ SignalComponent signal where
  toFun:=Quotient.map (projectSignal signal) (fun _ _ h=>component_project L signal h)
  invFun:=Quotient.map signalAnchor (fun _ _ h=>anchors_respect L signal existsColoring h)
  left_inv q:=Quotient.inductionOn q (fun v=>Quotient.sound (vertex_anchor L signal cover existsColoring v).symm)
  right_inv q:=Quotient.inductionOn q (fun _=>rfl)

include cover existsColoring in
 theorem graph_component_card : Nat.card ((graph L signal).Components Finset.univ)=Nat.card (SignalComponent signal) :=
  Nat.card_congr (graphComponentEquiv L signal cover existsColoring)

 include cover existsColoring in
 theorem coloring_count_components [Fintype S] [∀c,Fintype (W c)] :
    ProperColoringPottsReduction.properColoringCount (graph L signal) 3=
      6^((graph L signal).componentCount Finset.univ)*Nat.card (GlobalBits L signal) := by
  rw [ThreeColorPaletteCounting.properCount_eq_natCard,coloring_palette_count L signal cover,
    ←graph_component_card L signal cover existsColoring]
  rw [Nat.card_eq_fintype_card]
  rfl

end PlanarHom.PalettedColoringPatches
