import PlanarHom.RadialPottsStateGraph

/-! Actual contraction of each tile path to its two boundary ports. The
component equivalence includes every white vertex and every shared port. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile RadialPottsTile.OnionBoundary
variable {E : Type} [Fintype E] {k : ℕ}

abbrev BoundaryVertex (E : Type) (k : ℕ) := Medial.Dart E × Fin k
abbrev BoundaryEdge (E : Type) (k : ℕ) := E × Component k

def boundaryGraph (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool) (k : ℕ) :
    MultiGraph (BoundaryVertex E k) (BoundaryEdge E k) where
  src p := portImage rotation p.1 (sourcePort (choice p.1) p.2)
  dst p := portImage rotation p.1 (targetPort (choice p.1) p.2)

def boundaryAnchor (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool) :
    Vertex E k → BoundaryVertex E k
  | .inl (e,w) => portImage rotation e (sourcePort (choice e) (localComponent (choice e) (.inl w)))
  | .inr p => p

theorem state_local_reach (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool)
    (e : E) {u v : RadialPottsTile.Vertex k}
    (h : (localGraph k (choice e)).componentSetoid Finset.univ u v) :
    (stateGraph rotation choice k).componentSetoid Finset.univ (embed rotation e u) (embed rotation e v) := by
  induction h with
  | rel u v h =>
    obtain ⟨f,_,rfl,rfl⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨(e,f),Finset.mem_univ _,rfl,rfl⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

theorem vertex_to_boundaryAnchor (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool)
    (v : Vertex E k) :
    (stateGraph rotation choice k).componentSetoid Finset.univ v (.inr (boundaryAnchor rotation choice v)) := by
  cases v with
  | inr p => exact Relation.EqvGen.refl _
  | inl p => exact state_local_reach rotation choice p.1 (local_vertex_to_source (choice p.1) (.inl p.2))

private theorem anchor_to_source (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool)
    (e : E) (v : RadialPottsTile.Vertex k) :
    (boundaryGraph rotation choice k).componentSetoid Finset.univ
      (boundaryAnchor rotation choice (embed rotation e v))
      (portImage rotation e (sourcePort (choice e) (localComponent (choice e) v))) := by
  cases v with
  | inl w => exact Relation.EqvGen.refl _
  | inr p =>
    rcases local_port_cases (choice e) p with hp | hp
    · have h := congrArg (portImage rotation e) hp
      change (boundaryGraph rotation choice k).componentSetoid Finset.univ (portImage rotation e p) _
      rw [h]
    · have h := congrArg (portImage rotation e) hp
      change (boundaryGraph rotation choice k).componentSetoid Finset.univ (portImage rotation e p) _
      rw [h]
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        ⟨(e,localComponent (choice e) (.inr p)),Finset.mem_univ _,rfl,rfl⟩)

theorem state_reach_boundary (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool)
    {u v : Vertex E k} (h : (stateGraph rotation choice k).componentSetoid Finset.univ u v) :
    (boundaryGraph rotation choice k).componentSetoid Finset.univ
      (boundaryAnchor rotation choice u) (boundaryAnchor rotation choice v) := by
  induction h with
  | rel u v h =>
    obtain ⟨⟨e,f⟩,_,rfl,rfl⟩ := h
    have hc := (local_connected_iff (choice e) _ _).mp
      (Relation.EqvGen.rel _ _ ⟨f,Finset.mem_univ _,rfl,rfl⟩)
    have hu := anchor_to_source rotation choice e ((localGraph k (choice e)).src f)
    have hv := anchor_to_source rotation choice e ((localGraph k (choice e)).dst f)
    rw [hc] at hu
    exact Relation.EqvGen.trans _ _ _ hu (Relation.EqvGen.symm _ _ hv)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

theorem boundary_reach_state (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool)
    {u v : BoundaryVertex E k} (h : (boundaryGraph rotation choice k).componentSetoid Finset.univ u v) :
    (stateGraph rotation choice k).componentSetoid Finset.univ (.inr u) (.inr v) := by
  induction h with
  | rel u v h =>
    obtain ⟨⟨e,p⟩,_,rfl,rfl⟩ := h
    exact state_local_reach rotation choice e (local_port_pair (choice e) p)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

def boundaryComponentEquiv (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool) (k : ℕ) :
    (stateGraph rotation choice k).Components Finset.univ ≃ (boundaryGraph rotation choice k).Components Finset.univ where
  toFun := Quotient.map (boundaryAnchor rotation choice) (fun _ _ => state_reach_boundary rotation choice)
  invFun := Quotient.map Sum.inr (fun _ _ => boundary_reach_state rotation choice)
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h v => exact Quotient.sound (Relation.EqvGen.symm _ _ (vertex_to_boundaryAnchor rotation choice v))
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h v => rfl

theorem state_componentCount (rotation : Equiv.Perm (Medial.Dart E)) (choice : E → Bool) (k : ℕ) :
    (stateGraph rotation choice k).componentCount Finset.univ=(boundaryGraph rotation choice k).componentCount Finset.univ :=
  Fintype.card_congr (boundaryComponentEquiv rotation choice k)
end PlanarHom.RadialPotts.Assembly
