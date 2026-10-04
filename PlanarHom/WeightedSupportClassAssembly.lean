import PlanarHom.WeightedStructureTransport
import PlanarHom.SupportBlockSemantics
import Mathlib.Data.Fintype.Quotient

/-! Assemble exact structural support blocks using their genuine component
partition. Empty ambient color sets and arbitrary component cardinalities are
included; no independent matrix/weight permutation is introduced. -/
noncomputable section
open Classical
namespace PlanarHom.Structures
variable {C : Type} [Fintype C]

theorem weightedClass_of_supportBlocks (M : Matrix C C ℝ) (w : C→ℝ)
    (hs : ∀ i j,M i j=M j i)
    (hb : ∀ c : (RootedRestriction.colorSupport M hs).ConnectedComponent,
      AllowedWeightedBlock (fun i j : c.supp=>M i.val j.val) (fun i : c.supp=>w i.val)) :
    WeightedClass M w := by
  let G := RootedRestriction.colorSupport M hs
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let e := Fintype.equivFin G.ConnectedComponent
  let b : C→Fin (Fintype.card G.ConnectedComponent) := fun i=>e (G.connectedComponentMk i)
  have hsurj : Function.Surjective b := by
    intro r
    let c := e.symm r
    obtain ⟨i,hi⟩ := c.nonempty_supp
    refine ⟨i,?_⟩
    change e (G.connectedComponentMk i)=r
    change G.connectedComponentMk i=c at hi
    rw [hi]
    exact e.apply_symm_apply r
  refine ⟨Fintype.card G.ConnectedComponent,b,hsurj,?_,?_⟩
  · intro i j hij
    by_contra hn
    have hr : G.Reachable i j := by
      by_cases he:i=j
      · subst j; exact .rfl
      · exact (show G.Adj i j from ⟨he,hn⟩).reachable
    exact hij (congrArg e (SimpleGraph.ConnectedComponent.sound hr))
  · intro r
    let c := e.symm r
    have hp : ∀ i,b i=r ↔ i∈c.supp := by
      intro i
      change e (G.connectedComponentMk i)=r ↔ G.connectedComponentMk i=e.symm r
      exact e.apply_eq_iff_eq_symm_apply
    let er : {i // b i=r}≃c.supp := Equiv.subtypeEquivRight hp
    exact (hb c).equiv er

end PlanarHom.Structures
