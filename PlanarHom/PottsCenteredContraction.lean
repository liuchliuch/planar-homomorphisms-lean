import PlanarHom.OccurrenceEdgeContractionComponents
import PlanarHom.PottsCenteredPathAlgebra
import PlanarHom.FisherIncidenceOrdering
import Mathlib.Logic.Equiv.Prod

/-! Summing the literal degree-two vertex implements one actual edge contraction.
The proof sums its color and uses (qI-J)^2=q(qI-J). -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PottsCentered
open MultiGraph
variable {V E : Type} [Fintype V] [Fintype E] (G : MultiGraph V E)

theorem degree_two_other_edge (e : E) (hne : G.src e≠G.dst e)
    (hdeg : G.selectedDegree Finset.univ (G.dst e)=2) :
    ∃ f:E,f≠e ∧ ((G.src f=G.dst e ∧ G.dst f≠G.dst e) ∨
      (G.dst f=G.dst e ∧ G.src f≠G.dst e)) ∧
      ∀ g:E,g≠e → g≠f → G.src g≠G.dst e ∧ G.dst g≠G.dst e := by
  have hd : G.selectedDegree (Finset.univ.erase e) (G.dst e)=1 := by
    have hs := Finset.sum_erase_add Finset.univ (fun f => G.endpointCount f (G.dst e)) (Finset.mem_univ e)
    change G.selectedDegree (Finset.univ.erase e) (G.dst e)+G.endpointCount e (G.dst e)=
      G.selectedDegree Finset.univ (G.dst e) at hs
    simp [endpointCount,hne,hdeg] at hs
    omega
  rw [G.selectedDegree_eq_dartCount] at hd
  obtain ⟨d,hd⟩ := Fintype.card_eq_one_iff.mp hd
  rcases d with ⟨⟨f,b⟩,hf,hb⟩
  have hfe : f≠e := (Finset.mem_erase.mp hf).1
  have ho : ∀ g:E,g≠e → g≠f → G.src g≠G.dst e ∧ G.dst g≠G.dst e := by
    intro g hge hgf
    constructor
    · intro hs
      have hh := congrArg (fun z : {d : E×Bool // d.1∈Finset.univ.erase e ∧ G.dartVertex d=G.dst e} => z.val.1)
        (hd ⟨(g,false),by simp [hge],by simp [dartVertex,hs]⟩)
      exact hgf hh
    · intro ht
      have hh := congrArg (fun z : {d : E×Bool // d.1∈Finset.univ.erase e ∧ G.dartVertex d=G.dst e} => z.val.1)
        (hd ⟨(g,true),by simp [hge],by simp [dartVertex,ht]⟩)
      exact hgf hh
  refine ⟨f,hfe,?_,ho⟩
  cases b
  · left
    refine ⟨hb,?_⟩
    intro ht
    have hh := congrArg (fun z : {d : E×Bool // d.1∈Finset.univ.erase e ∧ G.dartVertex d=G.dst e} => z.val.2)
      (hd ⟨(f,true),hf,by simp [dartVertex,ht]⟩)
    cases hh
  · right
    refine ⟨hb,?_⟩
    intro hs
    have hh := congrArg (fun z : {d : E×Bool // d.1∈Finset.univ.erase e ∧ G.dartVertex d=G.dst e} => z.val.2)
      (hd ⟨(f,false),hf,by simp [dartVertex,hs]⟩)
    cases hh

private theorem contract_color_sum (q : ℕ) (e : E) (hne : G.src e≠G.dst e)
    (hdeg : G.selectedDegree Finset.univ (G.dst e)=2)
    (τ : {v : V // v≠G.dst e} → Fin q) :
    (∑ c : Fin q, ∏ g:E,interaction q
      ((Equiv.funSplitAt (G.dst e) (Fin q)).symm (c,τ) (G.src g))
      ((Equiv.funSplitAt (G.dst e) (Fin q)).symm (c,τ) (G.dst g)))=
      (q:ℚ)*∏ g : {g:E // g≠e},interaction q
        (τ ((G.contractEdge e hne).src g)) (τ ((G.contractEdge e hne).dst g)) := by
  obtain ⟨f,hfe,hfv,ho⟩ := degree_two_other_edge G e hne hdeg
  let split := Equiv.funSplitAt (G.dst e) (Fin q)
  let c₀ := τ ⟨G.src e,hne⟩
  let weight (c : Fin q) (g : E) := interaction q (split.symm (c,τ) (G.src g)) (split.symm (c,τ) (G.dst g))
  let rest := ∏ g∈(Finset.univ.erase e).erase f,weight c₀ g
  have hrest (c : Fin q) : (∏ g∈(Finset.univ.erase e).erase f,weight c g)=rest := by
    apply Finset.prod_congr rfl
    intro g hg
    have hgf := (Finset.mem_erase.mp hg).1
    have hge := (Finset.mem_erase.mp (Finset.mem_erase.mp hg).2).1
    obtain ⟨hs,ht⟩ := ho g hge hgf
    simp [weight,split,Equiv.funSplitAt_symm_apply,hs,ht]
  have hprod (c : Fin q) : (∏ g:E,weight c g)=interaction q c₀ c*weight c f*rest := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
    rw [← Finset.mul_prod_erase (Finset.univ.erase e) _ (show f ∈ Finset.univ.erase e from by simp [hfe]),hrest]
    have he : weight c e=interaction q c₀ c := by
      simp [weight,split,c₀,Equiv.funSplitAt_symm_apply,hne]
    rw [he,mul_assoc]
  have hsum : (∑ c : Fin q,interaction q c₀ c*weight c f)=(q:ℚ)*weight c₀ f := by
    rcases hfv with ⟨hs,ht⟩ | ⟨ht,hs⟩
    · simp only [weight,split,Equiv.funSplitAt_symm_apply,hs,dif_pos rfl,dif_neg ht,dite_true]
      exact interaction_comp q c₀ _
    · simp only [weight,split,Equiv.funSplitAt_symm_apply,ht,dif_pos rfl,dif_neg hs,dite_true]
      calc
        _ = ∑ c : Fin q,interaction q (τ ⟨G.src f,hs⟩) c*interaction q c c₀ := by
          apply Finset.sum_congr rfl
          intro c _
          rw [interaction_symmetric q c₀ c,mul_comm]
        _ = _ := interaction_comp q (τ ⟨G.src f,hs⟩) c₀
  have hcontract (g:E) : interaction q (τ (G.contractVertex e hne (G.src g)))
      (τ (G.contractVertex e hne (G.dst g)))=weight c₀ g := by
    simp only [weight,split,Equiv.funSplitAt_symm_apply,contractVertex]
    split_ifs <;> rfl
  have hrhs : (∏ g : {g:E // g≠e},interaction q
      (τ ((G.contractEdge e hne).src g)) (τ ((G.contractEdge e hne).dst g)))=weight c₀ f*rest := by
    simp only [contractEdge,hcontract]
    rw [← Finset.prod_subtype (Finset.univ.erase e) (by simp) (weight c₀)]
    rw [← Finset.mul_prod_erase (Finset.univ.erase e) _ (show f ∈ Finset.univ.erase e from by simp [hfe])]
  change (∑ c:Fin q,∏ g:E,weight c g)=_
  simp_rw [hprod]
  rw [← Finset.sum_mul,hsum,hrhs]
  ring

theorem unweighted_contract_degree_two (q : ℕ) (e : E) (hne : G.src e≠G.dst e)
    (hdeg : G.selectedDegree Finset.univ (G.dst e)=2) :
    G.unweighted (interactionMatrix q)=(q:ℚ)*(G.contractEdge e hne).unweighted (interactionMatrix q) := by
  rw [MultiGraph.unweighted_eq,MultiGraph.unweighted_eq]
  simp only [interactionMatrix_apply]
  let split := Equiv.funSplitAt (G.dst e) (Fin q)
  rw [Fintype.sum_equiv split _ (fun p => ∏ g:E,interaction q (split.symm p (G.src g)) (split.symm p (G.dst g)))
    (by intro σ; simp only [Equiv.symm_apply_apply])]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  dsimp only [split]
  simp_rw [contract_color_sum G q e hne hdeg]
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro τ _
  congr 1
end PlanarHom.PottsCentered
