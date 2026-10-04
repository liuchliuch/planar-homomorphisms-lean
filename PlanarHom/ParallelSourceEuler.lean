import PlanarHom.ParallelSourceFaceCycles
import PlanarHom.PottsComponentRank

/-! Full Euler and nonisolation are preserved by the actual inherited
parallel-copy rotation, including loops, disconnected graphs and empty graphs. -/
noncomputable section
open Classical
namespace PlanarHom.ParallelSource
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E}

 theorem thicken_connected_iff (n : ℕ) (a b : V) :
    (G.thicken (n+1)).componentSetoid Finset.univ a b ↔ G.componentSetoid Finset.univ a b := by
  constructor
  · intro h
    induction h with
    | rel a b h =>
      obtain ⟨⟨e,i⟩,_,rfl,rfl⟩ := h
      exact Relation.EqvGen.rel _ _ ⟨e,Finset.mem_univ _,rfl,rfl⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij
  · intro h
    induction h with
    | rel a b h =>
      obtain ⟨e,_,rfl,rfl⟩ := h
      exact Relation.EqvGen.rel _ _ ⟨(e,0),Finset.mem_univ _,rfl,rfl⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

 theorem thicken_componentCount (n : ℕ) :
    (G.thicken (n+1)).componentCount Finset.univ=G.componentCount Finset.univ :=
  Fintype.card_congr (Quotient.congr (Equiv.refl V) (thicken_connected_iff n))

 theorem parallel_euler (R : RotationRows G) (t : ℕ) (ht : 0<t)
    (he : Fintype.card V+count (R.rotation*reversePerm E)=
      Fintype.card E+2*G.componentCount Finset.univ) :
    Fintype.card V+count ((rows R t).rotation*reversePerm (E×Fin t))=
      Fintype.card (E×Fin t)+2*(G.thicken t).componentCount Finset.univ := by
  cases t with
  | zero => omega
  | succ n =>
      rw [parallel_face_count,thicken_componentCount,Fintype.card_prod,Fintype.card_fin,Nat.mul_add,Nat.mul_one]
      omega

 theorem parallel_incident (t : ℕ) (ht : 0<t)
    (hi : ∀v,∃a : Dart E,(G.dartPair a).1=v) :
    ∀v,∃a : Dart (E×Fin t),((G.thicken t).dartPair a).1=v := by
  intro v
  obtain ⟨a,ha⟩ := hi v
  refine ⟨copyDart a ⟨0,ht⟩,?_⟩
  rw [thicken_host,base_copy]
  exact ha
end PlanarHom.ParallelSource
