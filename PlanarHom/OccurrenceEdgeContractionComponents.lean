import PlanarHom.PlanarEdgeOperations
import PlanarHom.PottsRandomCluster
import PlanarHom.OccurrencePfaffianPairings

/-! Component and incidence bookkeeping for the actual occurrence contraction.
Loops created by contracting parallel edges remain literal loop occurrences. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
variable {V E : Type} [Fintype V] [Fintype E] (G : MultiGraph V E)
variable (e : E) (hne : G.src e≠G.dst e)

@[simp] theorem contractVertex_subtype (v : {v : V // v≠G.dst e}) :
    G.contractVertex e hne v.val=v := by
  simp [contractVertex,v.property]

@[simp] theorem contractVertex_src : G.contractVertex e hne (G.src e)=⟨G.src e,hne⟩ := by
  simp [contractVertex,hne]

@[simp] theorem contractVertex_dst : G.contractVertex e hne (G.dst e)=⟨G.src e,hne⟩ := by
  simp [contractVertex]

theorem vertex_reach_contract (v : V) :
    G.componentSetoid Finset.univ v (G.contractVertex e hne v).val := by
  by_cases h : v=G.dst e
  · subst v
    simpa using Relation.EqvGen.symm _ _
      (show G.componentSetoid Finset.univ (G.src e) (G.dst e) from
        Relation.EqvGen.rel _ _ ⟨e,Finset.mem_univ _,rfl,rfl⟩)
  · simp only [contractVertex,dif_neg h]
    exact Relation.EqvGen.refl _

theorem component_contract {u v : V} (h : G.componentSetoid Finset.univ u v) :
    (G.contractEdge e hne).componentSetoid Finset.univ (G.contractVertex e hne u) (G.contractVertex e hne v) := by
  induction h with
  | rel u v h =>
    obtain ⟨f,_,rfl,rfl⟩ := h
    by_cases hf : f=e
    · subst f
      rw [contractVertex_src,contractVertex_dst]
    · exact Relation.EqvGen.rel _ _ ⟨⟨f,hf⟩,Finset.mem_univ _,rfl,rfl⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

theorem contract_component {u v : {v : V // v≠G.dst e}}
    (h : (G.contractEdge e hne).componentSetoid Finset.univ u v) :
    G.componentSetoid Finset.univ u.val v.val := by
  induction h with
  | rel u v h =>
    obtain ⟨f,_,rfl,rfl⟩ := h
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (G.vertex_reach_contract e hne (G.src f.val)))
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨f.val,Finset.mem_univ _,rfl,rfl⟩)
        (G.vertex_reach_contract e hne (G.dst f.val)))
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

def contractComponentEquiv : G.Components Finset.univ ≃ (G.contractEdge e hne).Components Finset.univ where
  toFun := Quotient.map (G.contractVertex e hne) (fun _ _ => G.component_contract e hne)
  invFun := Quotient.map Subtype.val (fun _ _ => G.contract_component e hne)
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h v => exact Quotient.sound (Relation.EqvGen.symm _ _ (G.vertex_reach_contract e hne v))
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h v => simp

theorem componentCount_contract : (G.contractEdge e hne).componentCount Finset.univ=G.componentCount Finset.univ :=
  (Fintype.card_congr (G.contractComponentEquiv e hne)).symm

theorem contractVertex_eq_iff (w : V) (v : {v : V // v≠G.dst e}) :
    G.contractVertex e hne w=v ↔ w=v.val ∨ (w=G.dst e ∧ v.val=G.src e) := by
  by_cases hw : w=G.dst e
  · subst w
    simp [contractVertex,Subtype.ext_iff,Ne.symm v.property,eq_comm]
  · simp [contractVertex,hw,Subtype.ext_iff]

private theorem indicator_or (a b : Prop) [Decidable a] [Decidable b] (h : ¬ (a ∧ b)) :
    (if a ∨ b then 1 else 0 : ℕ)=(if a then 1 else 0)+(if b then 1 else 0) := by
  by_cases ha:a <;> by_cases hb:b <;> simp_all

theorem endpointCount_contract (f : {f : E // f≠e}) (v : {v : V // v≠G.dst e}) :
    (G.contractEdge e hne).endpointCount f v=
      G.endpointCount f.val v.val + if v.val=G.src e then G.endpointCount f.val (G.dst e) else 0 := by
  have hv := v.property
  simp only [endpointCount,contractEdge,contractVertex_eq_iff]
  rw [indicator_or _ _ (by rintro ⟨h₁,h₂,h₃⟩; exact hv (h₁.symm.trans h₂)),
      indicator_or _ _ (by rintro ⟨h₁,h₂,h₃⟩; exact hv (h₁.symm.trans h₂))]
  by_cases hw : v.val=G.src e
  · simp only [hw,and_true,ite_true]
    omega
  · simp only [hw,and_false,ite_false,add_zero]

private theorem degree_erase_edge (v : V) :
    (∑ f : {f : E // f≠e},G.endpointCount f.val v)+G.endpointCount e v=G.selectedDegree Finset.univ v := by
  rw [selectedDegree_eq_sum_endpointCount]
  have h := Finset.sum_erase_add Finset.univ (fun f => G.endpointCount f v) (Finset.mem_univ e)
  rw [← h]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.erase e) (by simp) (fun f => G.endpointCount f v)]

theorem degree_two_contract (hdeg : ∀ v,G.selectedDegree Finset.univ v=2)
    (v : {v : V // v≠G.dst e}) : (G.contractEdge e hne).selectedDegree Finset.univ v=2 := by
  rw [selectedDegree_eq_sum_endpointCount]
  simp_rw [endpointCount_contract]
  rw [Finset.sum_add_distrib]
  by_cases hv : v.val=G.src e
  · simp only [hv,ite_true]
    have hs := G.degree_erase_edge e (G.src e)
    have ht := G.degree_erase_edge e (G.dst e)
    simp [endpointCount,hne,Ne.symm hne,hdeg] at hs ht
    change (∑ x : {f : E // f≠e},G.endpointCount x.val (G.src e))=1 at hs
    change (∑ x : {f : E // f≠e},G.endpointCount x.val (G.dst e))=1 at ht
    omega
  · simp only [hv,if_false,Finset.sum_const_zero,add_zero]
    have h := G.degree_erase_edge e v.val
    have ht := v.property
    simp [endpointCount,Ne.symm hv,Ne.symm ht,hdeg] at h
    exact h
end PlanarHom.MultiGraph
