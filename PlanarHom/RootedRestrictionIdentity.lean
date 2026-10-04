import PlanarHom.RootedAttachmentTransport

/-! The complete fixed-field mathematical identity of source Lemma3.5,
including actual planarity of every rooted query. The encoded reduction and
support-component algorithm are separate modules. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.RootedRestriction
local instance (priority := 10000) rootedRestrictionIdentityDecEq0 (α : Type*) : DecidableEq α := Classical.decEq α
variable {K C : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype C]

/-- One fixed list of rooted planar graphs and coefficients works for every
finite rooted planar input. Signed edge weights are allowed. -/
theorem exists_fixed_planar_queries (M : Matrix C C K) (w : C → K)
    (hw : ∀ i, 0 < w i) (X : Set C) :
    ∃ n : ℕ, ∃ graphs : Fin n → FiniteRootedPlanar, ∃ c : Fin n → K,
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : RootedGraph V E), G.Planar →
        RootedGraph.restricted G M w X =
          ∑ j, c j * (RootedGraph.glue G (graphs j).2.2.val).partition M w := by
  obtain ⟨n,graphs,c,h⟩ := RootedSignatureSpan.exists_family_coefficients w hw
    (fun G : FiniteRootedPlanar => FiniteRootedPlanar.signature G M w)
    (fun i => if i ∈ X then 1 else 0)
  refine ⟨n,graphs,c,?_⟩
  intro V E _ _ G hG
  have hc := h (RootedGraph.finitePresentation G hG)
  rw [RootedGraph.signature_finitePresentation] at hc
  have hleft : RootedSignatureSpan.pairing w (fun i => if i ∈ X then 1 else 0)
      (RootedGraph.signature G M w) = RootedGraph.restricted G M w X := by
    simp [RootedSignatureSpan.pairing,RootedGraph.restricted,mul_ite,ite_mul]
  rw [hleft] at hc
  rw [hc]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [RootedGraph.partition_glue]
  unfold RootedSignatureSpan.pairing FiniteRootedPlanar.signature
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem queries_planar {V E : Type} [Finite V] [Finite E]
    (G : RootedGraph V E) (hG : G.Planar) (H : FiniteRootedPlanar) :
    (RootedGraph.glue G H.2.2.val).Planar := RootedGraph.glue_planar hG H.2.2.property

/-- The equivalent attachment formula at any host vertex, with all original
vertex and edge occurrences retained. -/
theorem exists_attachment_coefficients (M : Matrix C C K) (w : C → K)
    (hw : ∀ i, 0 < w i) (X : Set C) :
    ∃ n : ℕ, ∃ graphs : Fin n → FiniteRootedPlanar, ∃ c : Fin n → K,
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : MultiGraph V E) (r : V), G.Planar →
        RootedGraph.restricted (G.atRoot r) M w X =
          ∑ j, c j * (G.attachRooted (graphs j).2.2.val r).partition M w := by
  obtain ⟨n,graphs,c,h⟩ := exists_fixed_planar_queries M w hw X
  refine ⟨n,graphs,c,?_⟩
  intro V E _ _ G r hG
  have hp := (G.atRoot_planar_iff r).mpr hG
  rw [h _ _ (G.atRoot r) hp]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact ((MultiGraph.rootGlueEquiv G (graphs j).2.2.val r).partition M w).symm

end PlanarHom.RootedRestriction
