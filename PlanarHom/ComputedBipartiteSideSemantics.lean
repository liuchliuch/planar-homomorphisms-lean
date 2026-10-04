import PlanarHom.ComputedBipartiteSideQueries

/-! NEW exact sum of the two prescribed orientations on a connected input.
Contradictory parity instances have zero partition value for every crossing
matrix. No equality of the two orientation values is assumed. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.ComputedBipartiteSideQueries
open Complexity Complexity.MixedCode PrescribedDomains HomogeneousSourceOrientation
open BipartiteRankTwoTractability FixedRealRootRestrictions
variable {C K : Type} [Fintype C] [Field K]

def assignmentSide (g : MixedCode) (side : C→Bool) (σ : Fin g.vertices→C) (v : ℕ) : Bool :=
  if h : v<g.vertices then side (σ ⟨v,h⟩) else false

theorem nonzero_assignment_proper (g : MixedCode) (hg : g.Valid 1 0)
    (M : Matrix C C K) (w : C→K) (side : C→Bool)
    (hcross : ∀i j,M i j≠0 → side i≠side j) (σ : Fin g.vertices→C)
    (h : (g.toMultiGraph hg).assignmentWeight M w σ≠0) :
    Proper g (assignmentSide g side σ) := by
  intro e he
  obtain ⟨n,hn⟩ := List.get_of_mem he
  have hv:=hg.1 e he
  have hz:=RootedRestriction.assignment_edge_ne_zero g hg M w σ h n
  have hsrc : (g.toMultiGraph hg).src n=⟨e.1,hv.1⟩ := by
    apply Fin.ext; exact congrArg Prod.fst hn
  have hdst : (g.toMultiGraph hg).dst n=⟨e.2.1,hv.2.1⟩ := by
    apply Fin.ext; exact congrArg (fun p : ℕ×(ℕ×ℕ)=>p.2.1) hn
  rw [hsrc,hdst] at hz
  simpa only [assignmentSide,dif_pos hv.1,dif_pos hv.2.1] using hcross _ _ hz

theorem rejected_zero (g : MixedCode) (hg : g.Valid 1 0)
    (M : Matrix C C K) (w : C→K) (side : C→Bool)
    (hcross : ∀i j,M i j≠0 → side i≠side j) (hbad : (coloring g).1≠true) :
    (g.toMultiGraph hg).partition M w=0 := by
  apply Finset.sum_eq_zero
  intro σ _
  by_contra hz
  exact hbad ((coloring_complete g).mpr
    ⟨assignmentSide g side σ,nonzero_assignment_proper g hg M w side hcross σ hz⟩)

theorem query_valid (g : MixedCode) (hg : g.Valid 1 0) (flip : Bool) :
    (query flip g).Valid 1 2 := by
  rw [query_eq_withDomains g hg flip]
  exact withDomains_valid g hg (tag g flip)

theorem query_value (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (M : Matrix C C K) (w : C→K) (side : C→Bool)
    (hcross : ∀i j,M i j≠0 → side i≠side j) (hok : (coloring g).1=true) (flip : Bool) :
    totalEvaluation (fun _ : Fin 1=>M)
      (extendedUnaries (fun u : Fin 0=>u.elim0) (Bipartite.domains side)) w (query flip g)=
      (g.toMultiGraph hg).rootRestricted r M w (Bipartite.domains side (tag g flip r)) := by
  rw [query_eq_withDomains g hg flip]
  rw [totalEvaluation_valid _ _ _ _ (withDomains_valid g hg (tag g flip))]
  exact evaluate_withDomains_eq_rootRestricted_of_crosses g hg hc r M w side hcross
    (tag g flip) (tag_proper g hg hok flip)

theorem complementary_root_sums (g : MixedCode) (hg : g.Valid 1 0) (r : Fin g.vertices)
    (M : Matrix C C K) (w : C→K) (side : C→Bool) :
    (g.toMultiGraph hg).rootRestricted r M w (Bipartite.domains side (tag g false r))+
      (g.toMultiGraph hg).rootRestricted r M w (Bipartite.domains side (tag g true r))=
      (g.toMultiGraph hg).partition M w := by
  unfold MultiGraph.rootRestricted MultiGraph.partition
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  cases hs : side (σ r) <;> cases ht : decide (tag g false r=1) <;>
    simp [Bipartite.domains,tag_flip,hs,ht]

theorem queries_value_sum (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (hn : 0<g.vertices)
    (M : Matrix C C K) (w : C→K) (side : C→Bool)
    (hcross : ∀i j,M i j≠0 → side i≠side j) :
    ((queries g).map (totalEvaluation (fun _ : Fin 1=>M)
      (extendedUnaries (fun u : Fin 0=>u.elim0) (Bipartite.domains side)) w)).sum=
      g.evaluate hg (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w := by
  rw [evaluate_homogeneous]
  cases h : (coloring g).1
  · simp only [queries,h,Bool.false_eq_true,ite_false,List.map_nil,List.sum_nil]
    exact (rejected_zero g hg M w side hcross (by rw [h]; decide)).symm
  · simp only [queries,h,ite_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [query_value g hg hc ⟨0,hn⟩ M w side hcross h false,
      query_value g hg hc ⟨0,hn⟩ M w side hcross h true]
    exact complementary_root_sums g hg ⟨0,hn⟩ M w side

end PlanarHom.ComputedBipartiteSideQueries
