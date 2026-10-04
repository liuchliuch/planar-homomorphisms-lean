import PlanarHom.WeightedSupportClassAssembly

/-! NEW checked structural transport for the exact main predicates. The support
partition is literal numerical connectivity. No complexity classification is
asserted here. -/
noncomputable section
open Classical
namespace PlanarHom.Structures
variable {C D : Type}

theorem AllowedBlock.equiv {M : Matrix C C ℝ} (h : AllowedBlock M) (e : D≃C) :
    AllowedBlock (fun i j=>M (e i) (e j)) := by
  cases h with
  | zero c hz => exact .zero (e.trans c) (fun i j=>hz _ _)
  | positive k d hk a ρ ha hρ c hM =>
    exact .positive k d hk a ρ ha hρ (e.trans c) (fun i j=>hM _ _)
  | bipartite k l d hk hl a b ρ ha hb hρ c hM =>
    exact .bipartite k l d hk hl a b ρ ha hb hρ (e.trans c) (fun i j=>hM _ _)

theorem AllowedBlock.of_equiv {M : Matrix C C ℝ} (e : D≃C)
    (h : AllowedBlock (fun i j=>M (e i) (e j))) : AllowedBlock M := by
  simpa only [Equiv.apply_symm_apply] using h.equiv e.symm

variable [Fintype C]

theorem nonnegativeClass_of_supportBlocks (M : Matrix C C ℝ)
    (hs : ∀ i j,M i j=M j i)
    (hb : ∀ c : (RootedRestriction.colorSupport M hs).ConnectedComponent,
      AllowedBlock (fun i j : c.supp=>M i.val j.val)) : NonnegativeClass M := by
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
    exact (hb c).equiv (Equiv.subtypeEquivRight hp)

end PlanarHom.Structures
