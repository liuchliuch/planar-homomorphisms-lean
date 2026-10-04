import PlanarHom.SurfaceDualComponentConnectivity

/-! NEW exact disconnected correction: each non-isolated primal component has
one dual component, and each isolated vertex contributes the remaining primal
component. Both quotients and the equivalence are literal finite graph data. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceRibbonComplement
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G:MultiGraph V E} (R:RotationRows G)

 theorem isolated_related_eq (v:Isolated (G:=G)) {w:V}
    (h:G.componentSetoid Finset.univ v.val w) : w=v.val := by
  have he:G.EdgeConstant Finset.univ (fun u:V=>u=v.val) := by
    intro e he
    apply propext
    constructor
    · intro hs; exact (v.property (e,true) hs).elim
    · intro ht; exact (v.property (e,false) ht).elim
  have hh:=G.edgeConstant_respects Finset.univ (fun u:V=>u=v.val) he h
  exact Eq.mp hh rfl

 theorem dual_component_ne_isolated (p:R.dualGraph.Components Finset.univ) (v:Isolated (G:=G)) :
    R.dualComponentToPrimal p≠vertexComponent (G:=G) v.val := by
  intro h
  induction p using Quotient.inductionOn with | h f=>
    induction f using Quotient.inductionOn with | h a=>
      have hh:=isolated_related_eq v (Quotient.exact h.symm)
      exact v.property a hh

 def componentSumMap : R.dualGraph.Components Finset.univ⊕Isolated (G:=G)→G.Components Finset.univ
  | .inl p=>R.dualComponentToPrimal p
  | .inr v=>vertexComponent v.val

 theorem componentSumMap_injective : Function.Injective (componentSumMap R) := by
  intro a b h
  cases a with
  | inl p=>
    cases b with
    | inl q=>exact congrArg Sum.inl (R.dualComponentToPrimal_injective h)
    | inr v=>exact (dual_component_ne_isolated R p v h).elim
  | inr v=>
    cases b with
    | inl p=>exact (dual_component_ne_isolated R p v h.symm).elim
    | inr w=>
      congr 1
      apply Subtype.ext
      exact (isolated_related_eq v (Quotient.exact h)).symm

 theorem componentSumMap_surjective : Function.Surjective (componentSumMap R) := by
  intro c
  induction c using Quotient.inductionOn with | h v=>
    by_cases hv:∃a:Dart E,(G.dartPair a).1=v
    · obtain ⟨a,ha⟩:=hv
      refine ⟨.inl (Quotient.mk _ (R.faceOf a)),?_⟩
      change vertexComponent (G:=G) (G.dartPair a).1=vertexComponent v
      rw [ha]
    · exact ⟨.inr ⟨v,fun a ha=>hv ⟨a,ha⟩⟩,rfl⟩

 def componentSumEquiv : (R.dualGraph.Components Finset.univ⊕Isolated (G:=G))≃G.Components Finset.univ :=
  Equiv.ofBijective (componentSumMap R) ⟨componentSumMap_injective R,componentSumMap_surjective R⟩

 theorem dual_components_add_isolates :
    R.dualGraph.componentCount Finset.univ+Fintype.card (Isolated (G:=G))=G.componentCount Finset.univ := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (componentSumEquiv R)

end PlanarHom.SurfaceRibbonComplement
