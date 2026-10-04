import PlanarHom.PottsRandomCluster
import Mathlib.Data.Fintype.EquivFin

/-!
# Component rank bounds

Adding one edge occurrence merges at most two components. Consequently the
spanning-subgraph rank is bounded above by its number of edge occurrences,
including for multigraphs with loops and parallel edges.
-/
noncomputable section
open Classical

namespace PlanarHom.MultiGraph
variable {V E : Type*}

/-- The empty spanning subgraph has one component per vertex. -/
@[simp] theorem componentCount_empty [Fintype V] (G : MultiGraph V E) :
    G.componentCount ∅ = Fintype.card V := by
  symm
  apply Fintype.card_of_bijective (f := fun v => (Quotient.mk _ v : G.Components ∅))
  constructor
  · intro u v huv
    have h : G.EdgeConstant (∅ : Finset E) (id : V → V) := by
      intro e he
      simp at he
    exact G.edgeConstant_respects ∅ id h (Quotient.exact huv)
  · exact Quotient.mk_surjective

/-- Inserting one edge occurrence decreases the component count by at most one. -/
theorem componentCount_le_insert_add_one [Fintype V] (G : MultiGraph V E)
    (A : Finset E) (e : E) :
    G.componentCount A ≤ G.componentCount (insert e A) + 1 := by
  let q : V → G.Components A := Quotient.mk _
  let normalize : V → G.Components A :=
    fun v => if q v = q (G.src e) then q (G.dst e) else q v
  have hn : G.EdgeConstant (insert e A) normalize := by
    intro a ha
    rcases Finset.mem_insert.mp ha with hea | ha
    · subst a
      by_cases h : q (G.dst e) = q (G.src e)
      · simp [normalize, h]
      · simp [normalize]
    · have hq : q (G.src a) = q (G.dst a) :=
        Quotient.sound (Relation.EqvGen.rel _ _ ⟨a, ha, rfl, rfl⟩)
      simp only [normalize, hq]
  let f : G.Components (insert e A) → G.Components A :=
    Quotient.lift normalize (fun _ _ h => G.edgeConstant_respects _ _ hn h)
  have hs : Function.Surjective (Sum.elim f (fun _ : Unit => q (G.src e))) := by
    intro c
    induction c using Quotient.inductionOn with
    | h v =>
      by_cases hv : q v = q (G.src e)
      · exact ⟨Sum.inr (), hv.symm⟩
      · refine ⟨Sum.inl (Quotient.mk _ v), ?_⟩
        change normalize v = q v
        simp [normalize, hv]
  have hc := Fintype.card_le_of_surjective _ hs
  simpa [Fintype.card_sum, componentCount] using hc

/-- Inserting an occurrence with already connected endpoints does not merge components. -/
theorem componentCount_insert_of_related [Fintype V] (G : MultiGraph V E)
    (A : Finset E) (e : E) (h : G.componentSetoid A (G.src e) (G.dst e)) :
    G.componentCount (insert e A) = G.componentCount A := by
  let q : V → G.Components A := Quotient.mk _
  have hq : G.EdgeConstant (insert e A) q := by
    intro a ha
    rcases Finset.mem_insert.mp ha with hea | ha
    · subst a
      exact Quotient.sound h
    · exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨a, ha, rfl, rfl⟩)
  let f : G.Components (insert e A) → G.Components A :=
    Quotient.lift q (fun _ _ h => G.edgeConstant_respects _ _ hq h)
  have hf : Function.Surjective f := by
    intro c
    induction c using Quotient.inductionOn with
    | h v => exact ⟨Quotient.mk _ v, rfl⟩
  exact Nat.le_antisymm (G.componentCount_antitone (Finset.subset_insert e A))
    (Fintype.card_le_of_surjective f hf)

/-- Inserting an occurrence between distinct components merges exactly two components. -/
theorem componentCount_insert_add_one_of_not_related [Fintype V] (G : MultiGraph V E)
    (A : Finset E) (e : E) (h : ¬ G.componentSetoid A (G.src e) (G.dst e)) :
    G.componentCount (insert e A) + 1 = G.componentCount A := by
  let f : G.Components A → G.Components (insert e A) :=
    Quotient.map id (fun _ _ h => Relation.EqvGen.mono
      (fun _ _ ⟨a, ha, hu, hv⟩ => ⟨a, Finset.mem_insert_of_mem ha, hu, hv⟩) h)
  have hf : Function.Surjective f := by
    intro c
    induction c using Quotient.inductionOn with
    | h v => exact ⟨Quotient.mk _ v, rfl⟩
  have hne : G.componentCount (insert e A) ≠ G.componentCount A := by
    intro heq
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf, heq.symm⟩
    apply h
    apply Quotient.exact
    apply hbij.injective
    change (Quotient.mk _ (G.src e) : G.Components (insert e A)) =
      Quotient.mk _ (G.dst e)
    exact Quotient.sound (Relation.EqvGen.rel _ _
      ⟨e, Finset.mem_insert_self e A, rfl, rfl⟩)
  have hle := G.componentCount_antitone (Finset.subset_insert e A)
  have hone := G.componentCount_le_insert_add_one A e
  omega

/-- Every edge occurrence reduces the number of components by at most one. -/
theorem vertices_le_card_add_componentCount [Fintype V] (G : MultiGraph V E)
    (A : Finset E) :
    Fintype.card V ≤ A.card + G.componentCount A := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert e A he ih =>
    have hc := G.componentCount_le_insert_add_one A e
    rw [Finset.card_insert_of_notMem he]
    omega

/-- The rank of a spanning subgraph does not exceed its number of occurrences. -/
theorem rank_le_card [Fintype V] (G : MultiGraph V E) (A : Finset E) :
    Fintype.card V - G.componentCount A ≤ A.card := by
  have h := G.vertices_le_card_add_componentCount A
  omega

end PlanarHom.MultiGraph
