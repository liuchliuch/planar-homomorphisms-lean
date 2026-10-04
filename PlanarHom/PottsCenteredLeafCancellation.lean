import PlanarHom.PottsCenteredExpansion
import PlanarHom.FisherIncidenceOrdering
import Mathlib.Logic.Equiv.Prod

/-! NEW reconstruction: literal degree-one occurrence subsets contribute zero
to the centered expansion. The cancellation sums the actual leaf color. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PottsCentered
open MultiGraph
variable {V E : Type} [Fintype V] [Fintype E]

private theorem leaf_sum_zero (G : MultiGraph V E) (q : ℕ) (hq : 0<q)
    (A : Finset E) (v : V) (e : E) (he : e∈A)
    (hv : (G.src e=v ∧ G.dst e≠v) ∨ (G.dst e=v ∧ G.src e≠v))
    (ho : ∀ f∈A.erase e,G.src f≠v ∧ G.dst f≠v) :
    (∑ σ : V → Fin q,∏ f∈A,interaction q (σ (G.src f)) (σ (G.dst f)))=0 := by
  let split := Equiv.funSplitAt v (Fin q)
  let val (p : Fin q × ({x : V // x≠v} → Fin q)) :=
    ∏ f∈A,interaction q (split.symm p (G.src f)) (split.symm p (G.dst f))
  rw [Fintype.sum_equiv split _ val (by intro σ; simp [val])]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro τ _
  let σ₀ := split.symm (⟨0,hq⟩,τ)
  let rest := ∏ f∈A.erase e,interaction q (σ₀ (G.src f)) (σ₀ (G.dst f))
  have hr (c : Fin q) : (∏ f∈A.erase e,
      interaction q (split.symm (c,τ) (G.src f)) (split.symm (c,τ) (G.dst f)))=rest := by
    apply Finset.prod_congr rfl
    intro f hf
    rcases ho f hf with ⟨hs,ht⟩
    simp [split,σ₀,Equiv.funSplitAt_symm_apply,hs,ht]
  have hp (c : Fin q) : val (c,τ)=
      interaction q (split.symm (c,τ) (G.src e)) (split.symm (c,τ) (G.dst e))*rest := by
    dsimp only [val]
    rw [← Finset.mul_prod_erase A _ he,hr]
  simp_rw [hp]
  rw [← Finset.sum_mul]
  rcases hv with ⟨hs,ht⟩ | ⟨ht,hs⟩
  · simp only [split,Equiv.funSplitAt_symm_apply,hs,dif_pos rfl,dif_neg ht,dite_true]
    rw [show (∑ c : Fin q,interaction q c (τ ⟨G.dst e,ht⟩))=0 from by
      simpa only [interaction_symmetric] using interaction_rowSum q (τ ⟨G.dst e,ht⟩)]
    simp
  · simp only [split,Equiv.funSplitAt_symm_apply,ht,dif_pos rfl,dif_neg hs,dite_true]
    rw [interaction_rowSum]
    simp

/-- Every actual degree-one vertex makes the selected contribution vanish,
including parallel occurrences; a loop is counted twice and cannot be a leaf. -/
theorem selectedValue_eq_zero_of_degree_one (G : MultiGraph V E) (q : ℕ) (hq : 0<q)
    (A : Finset E) (v : V) (hv : G.selectedDegree A v=1) : selectedValue G q A=0 := by
  rw [G.selectedDegree_eq_dartCount] at hv
  obtain ⟨d,hd⟩ := Fintype.card_eq_one_iff.mp hv
  rcases d with ⟨⟨e,b⟩,he,hb⟩
  have ho : ∀ f∈A.erase e,G.src f≠v ∧ G.dst f≠v := by
    intro f hf
    have hfe := Finset.mem_erase.mp hf
    constructor
    · intro hs
      have hh := congrArg (fun z : {d : E × Bool // d.1∈A ∧ G.dartVertex d=v} => z.val.1)
        (hd ⟨(f,false),hfe.2,by simp [MultiGraph.dartVertex,hs]⟩)
      exact hfe.1 hh
    · intro ht
      have hh := congrArg (fun z : {d : E × Bool // d.1∈A ∧ G.dartVertex d=v} => z.val.1)
        (hd ⟨(f,true),hfe.2,by simp [MultiGraph.dartVertex,ht]⟩)
      exact hfe.1 hh
  have hend : (G.src e=v ∧ G.dst e≠v) ∨ (G.dst e=v ∧ G.src e≠v) := by
    cases b
    · left
      refine ⟨hb,?_⟩
      intro ht
      have hh := congrArg (fun z : {d : E × Bool // d.1∈A ∧ G.dartVertex d=v} => z.val.2)
        (hd ⟨(e,true),he,by simp [MultiGraph.dartVertex,ht]⟩)
      cases hh
    · right
      refine ⟨hb,?_⟩
      intro hs
      have hh := congrArg (fun z : {d : E × Bool // d.1∈A ∧ G.dartVertex d=v} => z.val.2)
        (hd ⟨(e,false),he,by simp [MultiGraph.dartVertex,hs]⟩)
      cases hh
  rw [selectedValue,leaf_sum_zero G q hq A v e he hend ho,mul_zero]
end PlanarHom.PottsCentered
