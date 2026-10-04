import PlanarHom.PottsRandomCluster

/-! Components of a literal permutation graph and its disjoint indexed copies. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
variable {D L : Type} [Fintype D] [Fintype L]

def permutationGraph (π : Equiv.Perm D) : MultiGraph D D := ⟨id,π⟩
def permutationLayerGraph (π : Equiv.Perm D) (L : Type) : MultiGraph (D × L) (D × L) :=
  ⟨id,fun p => (π p.1,p.2)⟩

theorem permutationLayer_reach {π : Equiv.Perm D} {u v : D × L}
    (h : (permutationLayerGraph π L).componentSetoid Finset.univ u v) :
    (permutationGraph π).componentSetoid Finset.univ u.1 v.1 ∧ u.2=v.2 := by
  induction h with
  | rel u v h =>
    obtain ⟨p,_,rfl,rfl⟩ := h
    exact ⟨Relation.EqvGen.rel _ _ ⟨p.1,Finset.mem_univ _,rfl,rfl⟩,rfl⟩
  | refl => exact ⟨Relation.EqvGen.refl _,rfl⟩
  | symm _ _ _ ih => exact ⟨Relation.EqvGen.symm _ _ ih.1,ih.2.symm⟩
  | trans _ _ _ _ _ ih ij => exact ⟨Relation.EqvGen.trans _ _ _ ih.1 ij.1,ih.2.trans ij.2⟩

theorem permutation_reach_layer {π : Equiv.Perm D} {u v : D}
    (h : (permutationGraph π).componentSetoid Finset.univ u v) (a : L) :
    (permutationLayerGraph π L).componentSetoid Finset.univ (u,a) (v,a) := by
  induction h with
  | rel u v h =>
    obtain ⟨d,_,rfl,rfl⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨(d,a),Finset.mem_univ _,rfl,rfl⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

def permutationLayerComponentEquiv (π : Equiv.Perm D) (L : Type) [Fintype L] :
    (permutationLayerGraph π L).Components Finset.univ ≃ ((permutationGraph π).Components Finset.univ × L) where
  toFun := Quotient.lift (fun p : D × L => (Quotient.mk _ p.1,p.2)) (by
    intro u v h
    have hh := permutationLayer_reach h
    exact Prod.ext (Quotient.sound hh.1) hh.2)
  invFun p := Quotient.lift (fun d => Quotient.mk _ (d,p.2))
    (fun _ _ h => Quotient.sound (permutation_reach_layer h p.2)) p.1
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h p => rfl
  right_inv p := by
    rcases p with ⟨x,a⟩
    induction x using Quotient.inductionOn with
    | h d => rfl

theorem permutationLayer_componentCount (π : Equiv.Perm D) :
    (permutationLayerGraph π L).componentCount Finset.univ=
      (permutationGraph π).componentCount Finset.univ*Fintype.card L := by
  rw [componentCount,Fintype.card_congr (permutationLayerComponentEquiv π L),Fintype.card_prod]
  rfl
end PlanarHom.MultiGraph
