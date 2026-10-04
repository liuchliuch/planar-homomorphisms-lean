import PlanarHom.RootedAttachmentTransport

/-! Root-domain sums are exactly the original assignment sums, with one root
condition and every original background factor retained. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.MultiGraph
local instance (priority := 10000) rootedConditionalSemanticsDecEq0 (α : Type*) : DecidableEq α := Classical.decEq α
variable {V E W F C R : Type*} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
variable [Fintype C] [CommSemiring R]

def rootRestricted (G : MultiGraph V E) (r : V) (M : Matrix C C R) (w : C → R) (X : Set C) : R :=
  ∑ σ : V → C, if σ r ∈ X then G.assignmentWeight M w σ else 0

theorem IncidenceEquiv.rootRestricted {G : MultiGraph V E} {H : MultiGraph W F}
    (e : IncidenceEquiv G H) (r : V) (M : Matrix C C R) (w : C → R) (X : Set C) :
    H.rootRestricted (e.vertex r) M w X = G.rootRestricted r M w X := by
  symm
  unfold MultiGraph.rootRestricted
  apply Fintype.sum_equiv (Equiv.arrowCongr e.vertex (Equiv.refl C))
  intro σ
  simp only [Equiv.arrowCongr,Equiv.coe_fn_mk,Equiv.refl_apply,Function.comp_apply,
    Equiv.symm_apply_apply]
  change (if σ r ∈ X then G.assignmentWeight M w σ else 0) =
    if σ r ∈ X then H.assignmentWeight M w (fun v => σ (e.vertex.symm v)) else 0
  rw [e.assignmentWeight]

end PlanarHom.MultiGraph
namespace PlanarHom.RootedGraph
local instance (priority := 10000) rootedConditionalSemanticsDecEq1 (α : Type*) : DecidableEq α := Classical.decEq α
variable {V E C R : Type*} [Fintype V] [Fintype E] [Fintype C] [CommSemiring R]

theorem sum_root_assignments (f : (PUnit.{1} ⊕ V → C) → R) :
    (∑ σ, f σ) = ∑ i : C, ∑ τ : V → C, f (extend i τ) := by
  rw [TwoTerminal.sum_colorings_sum]
  apply Fintype.sum_equiv (Equiv.funUnique PUnit C)
  intro σ
  apply Finset.sum_congr rfl
  intro τ _
  congr 1

theorem restricted_eq_rootRestricted (G : RootedGraph V E) (M : Matrix C C R)
    (w : C → R) (X : Set C) :
    restricted G M w X = G.rootRestricted (.inl PUnit.unit) M w X := by
  unfold MultiGraph.rootRestricted
  rw [sum_root_assignments]
  unfold restricted
  apply Finset.sum_congr rfl
  intro i _
  simp only [extend,Sum.elim_inl]
  by_cases hi : i ∈ X
  · simp only [hi,ite_true,signature,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    exact (assignment_extend G M w i τ).symm
  · simp [hi]

end PlanarHom.RootedGraph
namespace PlanarHom.MultiGraph
local instance (priority := 10000) rootedConditionalSemanticsDecEq2 (α : Type*) : DecidableEq α := Classical.decEq α
variable {V E C R : Type*} [Fintype V] [Fintype E] [Fintype C] [CommSemiring R]

theorem atRoot_restricted (G : MultiGraph V E) (r : V) (M : Matrix C C R)
    (w : C → R) (X : Set C) :
    RootedGraph.restricted (G.atRoot r) M w X = G.rootRestricted r M w X := by
  rw [RootedGraph.restricted_eq_rootRestricted]
  simpa only [atRoot,MultiGraph.reindexEquiv,rootEquiv_root] using (G.reindexEquiv (rootEquiv r) (Equiv.refl E)).rootRestricted r M w X

end PlanarHom.MultiGraph
