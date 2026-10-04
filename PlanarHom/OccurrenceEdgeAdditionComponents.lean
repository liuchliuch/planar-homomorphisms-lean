import PlanarHom.PlanarEdgeOperations
import PlanarHom.PottsComponentRank

/-! Exact component changes for physically adding an occurrence. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
variable {V E : Type} [Fintype V] [Fintype E] (G : MultiGraph V E)

local instance (priority := high) : DecidableEq (E ⊕ Unit) := Classical.decEq _

def oldWithEdges : Finset (E ⊕ Unit) := Finset.univ.filter (fun e : E ⊕ Unit => e.isLeft=true)

@[simp] theorem mem_oldWithEdges (e : E ⊕ Unit) : e∈oldWithEdges (E:=E) ↔ e.isLeft := by simp [oldWithEdges]

theorem withEdge_old_relation (a b u v : V) :
    (G.withEdge a b).componentSetoid (oldWithEdges (E:=E)) u v ↔ G.componentSetoid Finset.univ u v := by
  constructor
  · intro h
    induction h with
    | rel u v h =>
      obtain ⟨e,he,rfl,rfl⟩ := h
      cases e with
      | inl e => exact Relation.EqvGen.rel _ _ ⟨e,Finset.mem_univ _,rfl,rfl⟩
      | inr x => simp at he
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij
  · intro h
    induction h with
    | rel u v h =>
      obtain ⟨e,he,rfl,rfl⟩ := h
      exact Relation.EqvGen.rel _ _ ⟨.inl e,by simp,rfl,rfl⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

theorem withEdge_old_count (a b : V) :
    (G.withEdge a b).componentCount (oldWithEdges (E:=E))=G.componentCount Finset.univ :=
  Fintype.card_congr (Quotient.congr (Equiv.refl V) (G.withEdge_old_relation a b))

theorem insert_oldWithEdges : insert (.inr ()) (oldWithEdges (E:=E))=Finset.univ := by
  ext x
  cases x <;> simp

theorem componentCount_le_withEdge_add_one (a b : V) :
    G.componentCount Finset.univ≤(G.withEdge a b).componentCount Finset.univ+1 := by
  have h := (G.withEdge a b).componentCount_le_insert_add_one (oldWithEdges (E:=E)) (.inr ())
  rwa [withEdge_old_count,insert_oldWithEdges] at h

theorem withEdge_count_of_related (a b : V) (h : G.componentSetoid Finset.univ a b) :
    (G.withEdge a b).componentCount Finset.univ=G.componentCount Finset.univ := by
  have hh := (G.withEdge a b).componentCount_insert_of_related (oldWithEdges (E:=E)) (.inr ())
    ((G.withEdge_old_relation a b a b).mpr h)
  rwa [insert_oldWithEdges,withEdge_old_count] at hh

theorem withEdge_count_of_not_related (a b : V) (h : ¬G.componentSetoid Finset.univ a b) :
    (G.withEdge a b).componentCount Finset.univ+1=G.componentCount Finset.univ := by
  have hh := (G.withEdge a b).componentCount_insert_add_one_of_not_related (oldWithEdges (E:=E)) (.inr ())
    (fun hn => h ((G.withEdge_old_relation a b a b).mp hn))
  rwa [insert_oldWithEdges,withEdge_old_count] at hh
end PlanarHom.MultiGraph
