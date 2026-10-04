import PlanarHom.PottsCenteredContraction
import PlanarHom.OccurrenceMatchings
import Mathlib.Logic.Equiv.Option

/-! Evaluation of every finite occurrence multigraph of degree two. Nonloop
contraction reduces the number of vertices; the terminal loop-only graph is
computed directly. Empty graphs, single loops and parallel pairs are included. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PottsCentered
open MultiGraph
variable {V E : Type} [Fintype V] [Fintype E]

private def loopComponentEquiv (G : MultiGraph V E) (hloop : ∀e,G.src e=G.dst e) :
    G.Components Finset.univ ≃ V where
  toFun := Quotient.lift id (fun _ _ h => G.edgeConstant_respects Finset.univ id (fun e _ => hloop e) h)
  invFun := Quotient.mk _
  left_inv x := by induction x using Quotient.inductionOn with | h v => rfl
  right_inv _ := rfl

private theorem unweighted_all_loops (G : MultiGraph V E) (q : ℕ)
    (hloop : ∀e,G.src e=G.dst e) (hdeg : ∀v,G.selectedDegree Finset.univ v=2) :
    G.unweighted (interactionMatrix q)=(q:ℚ)^Fintype.card V*((q:ℚ)-1)^G.componentCount Finset.univ := by
  have hc : G.componentCount Finset.univ=Fintype.card V := Fintype.card_congr (loopComponentEquiv G hloop)
  have hd := G.sum_selectedDegree Finset.univ
  simp only [hdeg,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hd
  have he : Fintype.card E=Fintype.card V := by omega
  rw [MultiGraph.unweighted_eq]
  simp only [interactionMatrix_apply,hloop,interaction,ite_true,Finset.prod_const,Finset.card_univ,
    Finset.sum_const,smul_eq_mul,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  rw [he,hc]
  simp [nsmul_eq_mul]

private theorem unweighted_degree_two_aux (q n : ℕ) :
    ∀ (V E : Type) [Fintype V] [Fintype E] (G : MultiGraph V E), Fintype.card V=n →
      (∀v,G.selectedDegree Finset.univ v=2) →
      G.unweighted (interactionMatrix q)=(q:ℚ)^Fintype.card V*((q:ℚ)-1)^G.componentCount Finset.univ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E _ _ G hn hdeg
    by_cases hloop : ∀e,G.src e=G.dst e
    · exact unweighted_all_loops G q hloop hdeg
    · push_neg at hloop
      obtain ⟨e,hne⟩ := hloop
      have hc : Fintype.card {v : V // v≠G.dst e}+1=Fintype.card V := by
        simpa only [Fintype.card_option] using Fintype.card_congr (Equiv.optionSubtypeNe (G.dst e))
      have hlt : Fintype.card {v : V // v≠G.dst e}<n := by omega
      have hh := ih _ hlt _ _ (G.contractEdge e hne) rfl (G.degree_two_contract e hne hdeg)
      rw [unweighted_contract_degree_two G q e hne (hdeg _),hh,G.componentCount_contract e hne]
      rw [← hc,pow_succ]
      ring

/-- Literal unnormalized value, valid even for zero colors. -/
theorem unweighted_degree_two (G : MultiGraph V E) (q : ℕ)
    (hdeg : ∀v,G.selectedDegree Finset.univ v=2) :
    G.unweighted (interactionMatrix q)=(q:ℚ)^Fintype.card V*((q:ℚ)-1)^G.componentCount Finset.univ :=
  unweighted_degree_two_aux q (Fintype.card V) V E G rfl hdeg

/-- The coefficient's actual vertex normalization leaves one q−1 per component. -/
theorem normalized_degree_two (G : MultiGraph V E) (q : ℕ) (hq : 0<q)
    (hdeg : ∀v,G.selectedDegree Finset.univ v=2) :
    (q:ℚ)⁻¹^Fintype.card V*G.unweighted (interactionMatrix q)=((q:ℚ)-1)^G.componentCount Finset.univ := by
  rw [unweighted_degree_two G q hdeg,← mul_assoc,← mul_pow,inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hq)]
  simp
end PlanarHom.PottsCentered
