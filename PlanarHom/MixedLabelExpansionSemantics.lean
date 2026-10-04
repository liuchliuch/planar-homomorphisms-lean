import PlanarHom.MixedLabelExpansionMachines

/-! Exact entrywise product semantics of fixed binary label words. -/
namespace PlanarHom.Complexity.MixedCode
noncomputable section
open PlanarHom.FiniteLabelWordLookupMachines
open scoped BigOperators
variable {C R : Type} [Fintype C] [CommSemiring R]

def wordMatrices {a b : ℕ} (ρ : Fin a→List (Fin b)) (M : Fin b→Matrix C C R) :
    Fin a→Matrix C C R := fun i x y => ((ρ i).map (fun label => M label x y)).prod

theorem evaluate_expandBinaryWords {a b u : ℕ} (g : MixedCode) (hg : g.Valid a u)
    (ρ : Fin a→List (Fin b)) (M : Fin b→Matrix C C R) (U : Fin u→C→R) (w : C→R) :
    (g.expandBinaryWords (finTable ρ)).evaluate
      (expandBinaryWords_valid _ hg (lookup_finTable_lt ρ)) M U w =
      g.evaluate hg (wordMatrices ρ M) U w := by
  unfold evaluate expandBinaryWords
  apply Finset.sum_congr rfl
  intro σ _
  have hprod :
      ((g.edges.flatMap (fun e => (lookup (finTable ρ) e.2.2).map
        (fun label => (e.1,e.2.1,label)))).map (binaryValue g.vertices b M σ)).prod =
      (g.edges.map (binaryValue g.vertices a (wordMatrices ρ M) σ)).prod := by
    rw [List.map_flatMap,List.flatMap_def,List.prod_flatten,List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro e he
    have hv := hg.1 e he
    dsimp only [Function.comp_apply]
    rw [lookup_finTable ρ ⟨e.2.2,hv.2.2⟩]
    rw [binaryValue,dif_pos hv]
    simp only [wordMatrices,List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro label _
    change binaryValue g.vertices b M σ (e.1,e.2.1,label.val)=_
    rw [binaryValue,dif_pos ⟨hv.1,hv.2.1,label.isLt⟩]
  rw [hprod]

end
end PlanarHom.Complexity.MixedCode
