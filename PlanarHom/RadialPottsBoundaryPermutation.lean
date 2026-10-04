import PlanarHom.RadialPottsBoundaryReduction
import PlanarHom.PermutationGraphComponents

/-! The contracted radial boundary consists of exactly k copies of the
literal selected-edge boundary permutation of the source rotation. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile RadialPottsTile.OnionBoundary
variable {E : Type} [Fintype E] {k : ℕ}

def selectedFlip (choice : E → Bool) : Equiv.Perm (Medial.Dart E) where
  toFun d := (d.1,if choice d.1 then !d.2 else d.2)
  invFun d := (d.1,if choice d.1 then !d.2 else d.2)
  left_inv d := by rcases d with ⟨e,b⟩; cases hc : choice e <;> cases b <;> simp [hc]
  right_inv d := by rcases d with ⟨e,b⟩; cases hc : choice e <;> cases b <;> simp [hc]

def boundaryPermutation (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool) :
    Equiv.Perm (Medial.Dart E) := (selectedFlip choice).trans rotation.symm

def boolFin (b : Bool) : Fin 2 := if b then 1 else 0

def boundaryEdgeOf (choice : E → Bool) (p : BoundaryVertex E k) : BoundaryEdge E k :=
  (p.1.1,(boolFin p.1.2,if choice p.1.1 then p.2 else reverseLane p.2))

def boundaryEdgeLayer (choice : E → Bool) (p : BoundaryEdge E k) : BoundaryVertex E k :=
  ((p.1,decide (p.2.1.val=1)),if choice p.1 then p.2.2 else reverseLane p.2.2)

@[simp] theorem boundaryEdgeOf_layer (choice : E → Bool) (p : BoundaryEdge E k) :
    boundaryEdgeOf choice (boundaryEdgeLayer choice p)=p := by
  rcases p with ⟨e,c,a⟩
  fin_cases c <;> cases hc : choice e <;> simp [boundaryEdgeOf,boundaryEdgeLayer,boolFin,hc]

@[simp] theorem boundaryEdgeLayer_of (choice : E → Bool) (p : BoundaryVertex E k) :
    boundaryEdgeLayer choice (boundaryEdgeOf choice p)=p := by
  rcases p with ⟨⟨e,b⟩,a⟩
  cases b <;> cases hc : choice e <;> simp [boundaryEdgeOf,boundaryEdgeLayer,boolFin,hc]

theorem boundaryEdgeOf_src (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool)
    (p : BoundaryVertex E k) :
    (boundaryGraph rotation choice k).src (boundaryEdgeOf choice p)=
      if choice p.1.1 then p else (boundaryPermutation rotation choice p.1,p.2) := by
  rcases p with ⟨⟨e,b⟩,a⟩
  cases b <;> cases hc : choice e <;>
    simp [boundaryGraph,boundaryEdgeOf,sourcePort,portImage,boolFin,boundaryPermutation,selectedFlip,
      rotateSide,oddBit,endBit,hc]

theorem boundaryEdgeOf_dst (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool)
    (p : BoundaryVertex E k) :
    (boundaryGraph rotation choice k).dst (boundaryEdgeOf choice p)=
      if choice p.1.1 then (boundaryPermutation rotation choice p.1,p.2) else p := by
  rcases p with ⟨⟨e,b⟩,a⟩
  cases b <;> cases hc : choice e <;>
    simp [boundaryGraph,boundaryEdgeOf,targetPort,portImage,boolFin,boundaryPermutation,selectedFlip,
      rotateSide,oddBit,endBit,hc]

theorem boundary_reach_layer (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool)
    {u v : BoundaryVertex E k} (h : (boundaryGraph rotation choice k).componentSetoid Finset.univ u v) :
    (permutationLayerGraph (boundaryPermutation rotation choice) (Fin k)).componentSetoid Finset.univ u v := by
  induction h with
  | rel u v h =>
    obtain ⟨p,_,rfl,rfl⟩ := h
    have hp := boundaryEdgeOf_layer choice p
    rw [← hp,boundaryEdgeOf_src,boundaryEdgeOf_dst]
    split_ifs
    · exact Relation.EqvGen.rel _ _ ⟨boundaryEdgeLayer choice p,Finset.mem_univ _,rfl,rfl⟩
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        ⟨boundaryEdgeLayer choice p,Finset.mem_univ _,rfl,rfl⟩)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

theorem layer_reach_boundary (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool)
    {u v : BoundaryVertex E k}
    (h : (permutationLayerGraph (boundaryPermutation rotation choice) (Fin k)).componentSetoid Finset.univ u v) :
    (boundaryGraph rotation choice k).componentSetoid Finset.univ u v := by
  induction h with
  | rel u v h =>
    obtain ⟨p,_,rfl,rfl⟩ := h
    have hp : (boundaryGraph rotation choice k).componentSetoid Finset.univ
        ((boundaryGraph rotation choice k).src (boundaryEdgeOf choice p))
        ((boundaryGraph rotation choice k).dst (boundaryEdgeOf choice p)) :=
      Relation.EqvGen.rel _ _ ⟨boundaryEdgeOf choice p,Finset.mem_univ _,rfl,rfl⟩
    rw [boundaryEdgeOf_src,boundaryEdgeOf_dst] at hp
    split_ifs at hp
    · exact hp
    · exact Relation.EqvGen.symm _ _ hp
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

def boundaryLayerComponentEquiv (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool) (k : ℕ) :
    (boundaryGraph rotation choice k).Components Finset.univ ≃
      (permutationLayerGraph (boundaryPermutation rotation choice) (Fin k)).Components Finset.univ where
  toFun := Quotient.map id (fun _ _ => boundary_reach_layer rotation choice)
  invFun := Quotient.map id (fun _ _ => layer_reach_boundary rotation choice)
  left_inv x := by induction x using Quotient.inductionOn with | h p => rfl
  right_inv x := by induction x using Quotient.inductionOn with | h p => rfl

theorem state_componentCount_boundaryPermutation (rotation : Equiv.Perm (Medial.Dart E))
    (choice : E → Bool) (k : ℕ) :
    (stateGraph rotation choice k).componentCount Finset.univ=
      (permutationGraph (boundaryPermutation rotation choice)).componentCount Finset.univ*k := by
  rw [state_componentCount,componentCount,Fintype.card_congr (boundaryLayerComponentEquiv rotation choice k)]
  exact (permutationLayer_componentCount (L:=Fin k) (boundaryPermutation rotation choice)).trans (by simp)
end PlanarHom.RadialPotts.Assembly
