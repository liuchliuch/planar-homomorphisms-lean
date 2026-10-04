import PlanarHom.FisherExpansionIsolates
import PlanarHom.FisherRotationConnected

/-! NEW complete finite Fisher Euler transfer on an actual connected source
component. Isolated source vertices are included by their explicit output faces. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}

 theorem expansion_euler_component [Nonempty V] (o : G.IncidenceOrdering)
    (hG : ∀u v,G.componentSetoid Finset.univ u v)
    (heuler : Nonempty E → Fintype.card V+count o.rotationRows.facePerm=Fintype.card E+2) :
    Fintype.card (ExpansionVertex o)+count (expansionRows o).facePerm=Fintype.card (ExpansionEdge o)+2 := by
  rcases isEmpty_or_nonempty E with hE|hE
  · letI := hE
    have hz : ∀v,o.degree v=0 := by
      intro v
      rw [o.degree_eq]
      simp [selectedDegree]
    exact expansion_euler_isolated o hz (vertex_card_one_of_connected hG)
  · letI := hE
    exact expansion_euler o (degree_pos_of_connected o hG) (heuler hE)

 def graphEqRows {W F : Type*} {H J : MultiGraph W F} [DecidableEq (Dart F)]
    (h : H=J) (R : RotationRows H) : RotationRows J := h ▸ R

 theorem graphEqRows_face {W F : Type*} [Fintype W] [Fintype F]
    {H J : MultiGraph W F} [DecidableEq (Dart F)] (h : H=J) (R : RotationRows H) :
    (graphEqRows h R).facePerm=R.facePerm := by cases h; rfl

 def recodeRows {W F : Type*} {H : MultiGraph W F} {d : DecidableEq (Dart F)}
    (d' : DecidableEq (Dart F)) (R : @RotationRows W F H d) : @RotationRows W F H d' where
  row := @RotationRows.row W F H d R
  nodup := @RotationRows.nodup W F H d R
  mem := @RotationRows.mem W F H d R

 theorem recodeRows_face {W F : Type*} {H : MultiGraph W F} {d : DecidableEq (Dart F)}
    (d' : DecidableEq (Dart F)) (R : @RotationRows W F H d) :
    @RotationRows.facePerm W F d' H (recodeRows d' R)=@RotationRows.facePerm W F d H R := by
  have h : d=d' := Subsingleton.elim _ _
  cases h
  rfl

 theorem ordering_face_decidable (o : G.IncidenceOrdering) (d d' : DecidableEq (Dart E)) :
    @RotationRows.facePerm V E d G (@IncidenceOrdering.rotationRows V E G d o)=
      @RotationRows.facePerm V E d' G (@IncidenceOrdering.rotationRows V E G d' o) := by
  have h : d=d' := Subsingleton.elim _ _
  cases h
  rfl

 def inheritedFisherRows (o : G.IncidenceOrdering)
    (p : (ExpansionVertex o×Fin 3)≃(ExpansionEdge o×Bool))
    (hp : cubicOriginal p=expansionGraph o) : RotationRows (cubicDecoration p) :=
  recodeRows (Classical.decEq _) (cubicInheritedRows p (graphEqRows hp.symm (expansionRows o)))

 theorem inheritedFisher_euler_component [Nonempty V] (o : G.IncidenceOrdering)
    (hG : ∀u v,G.componentSetoid Finset.univ u v)
    (heuler : Nonempty E → Fintype.card V+count o.rotationRows.facePerm=Fintype.card E+2)
    (p : (ExpansionVertex o×Fin 3)≃(ExpansionEdge o×Bool))
    (hp : cubicOriginal p=expansionGraph o) :
    Fintype.card (ExpansionVertex o×Fin 3)+count (inheritedFisherRows o p hp).facePerm=
      Fintype.card (ExpansionEdge o⊕(ExpansionVertex o×Fin 3))+2 := by
  rw [inheritedFisherRows,recodeRows_face (Classical.decEq _)
    (cubicInheritedRows p (graphEqRows hp.symm (expansionRows o)))]
  apply cubicInherited_euler p (graphEqRows hp.symm (expansionRows o))
  rw [graphEqRows_face]
  exact expansion_euler_component o hG heuler

 theorem inheritedFisher_connected (o : G.IncidenceOrdering)
    (hG : ∀u v,G.componentSetoid Finset.univ u v)
    (p : (ExpansionVertex o×Fin 3)≃(ExpansionEdge o×Bool))
    (hp : cubicOriginal p=expansionGraph o) :
    ∀u v,(cubicDecoration p).componentSetoid Finset.univ u v := by
  apply cubicInherited_connected p (graphEqRows hp.symm (expansionRows o))
  rw [hp]
  exact expansion_connected o hG

 theorem incidenceOrdering_face [DecidableEq (Dart E)] (R : RotationRows G) :
    R.incidenceOrdering.rotationRows.facePerm=R.facePerm := by
  rw [RotationRows.facePerm,RotationRows.facePerm,R.incidenceOrdering_rotation]

/-- A proved sphere rotation of the source component produces a proved sphere
rotation of its full Fisher graph, in any cubic port naming. -/
theorem fisher_euler_from_rotation [Nonempty V] [DecidableEq (Dart E)] (R : RotationRows G)
    (hG : ∀u v,G.componentSetoid Finset.univ u v)
    (heuler : Nonempty E → Fintype.card V+count R.facePerm=Fintype.card E+2)
    (p : (ExpansionVertex R.incidenceOrdering×Fin 3)≃(ExpansionEdge R.incidenceOrdering×Bool))
    (hp : cubicOriginal p=expansionGraph R.incidenceOrdering) :
    Fintype.card (ExpansionVertex R.incidenceOrdering×Fin 3)+
      count (inheritedFisherRows R.incidenceOrdering p hp).facePerm=
      Fintype.card (ExpansionEdge R.incidenceOrdering⊕(ExpansionVertex R.incidenceOrdering×Fin 3))+2 := by
  apply inheritedFisher_euler_component R.incidenceOrdering hG _ p hp
  intro hE
  apply (congrArg (fun k : ℕ=>Fintype.card V+k) ?_).trans (heuler hE)
  apply congrArg count
  exact (ordering_face_decidable R.incidenceOrdering _ _).trans (incidenceOrdering_face R)


end PlanarHom.Fisher
