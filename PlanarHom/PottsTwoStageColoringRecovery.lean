import PlanarHom.PottsTwoStageTotalRecovery

/-! Direct recovery of the counting seed's proper three-colorings. Evaluating
at edge parameter -1 avoids an extra positive-three-state interpolation layer. -/
noncomputable section
open Classical
namespace PlanarHom.PottsTwoStageMachines
open Complexity Complexity.MixedCode PairProjectionMachines MultiGraph PottsTwoStageInterpolation
open ProperColoringPottsReduction

 theorem randomCluster_coloring {V E : Type} [Fintype V] [Fintype E]
    (G : MultiGraph V E) (q : ℕ) :
    G.randomCluster q (-1)=G.unweighted (coloringMatrix q) := by
  rw [←G.weighted_randomCluster q (-1)]
  have he : (fun i j : Fin q => (if i=j then (-1:ℚ) else 0)+1)=coloringMatrix q := by
    funext i j
    by_cases h : i=j <;> simp [coloringMatrix,h]
  rw [he]

 def recoverThreeColoring (δ : ℚ) (p : Input) : ℚ := if p.1=0 then 1 else recover δ 3 (-1) p

 theorem fp_recoverThreeColoring (δ : ℚ) : FP inputEncoding fieldCode (recoverThreeColoring δ) := by
  have hn := (fp_fst BitEncoding.unaryNat (BitEncoding.unaryNat.prod fieldCode.list)).comp
    UnaryNatConversionMachine.fp_conversion
  have hz := (hn.pair (fp_const inputEncoding BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  exact (hz.ite (fp_const inputEncoding fieldCode (1:ℚ)) (fp_recover δ 3 (-1))).congr
    (fun _ => by simp [recoverThreeColoring])

 theorem recoverThreeColoring_radialAnswers (g : MixedCode) (hg : g.Valid 1 0)
    (δ : ℚ) (hδ : 1<δ) (answers : List ℚ)
    (ha : ∀ k<g.vertices,∀ l<g.edges.length+1,
      answers.getD (k*(g.edges.length+1)+l) 0=
        radialValue ((g.parallelLabel 0 (l+1)).toMultiGraph
          (MixedCode.parallelLabel_valid 0 (l+1) 1 0 g hg)) δ (k+1)) :
    recoverThreeColoring δ (g.vertices,(g.edges.length,answers))=
      (g.toMultiGraph hg).unweighted (coloringMatrix 3) := by
  by_cases hn : g.vertices=0
  · letI : IsEmpty (Fin g.vertices) := by rw [hn]; infer_instance
    simp only [recoverThreeColoring,hn,ite_true]
    exact (unweighted_empty_source _ _).symm
  · letI : Nonempty (Fin g.vertices) := ⟨⟨0,Nat.pos_of_ne_zero hn⟩⟩
    rw [recoverThreeColoring,if_neg hn]
    have hh := recover_randomCluster_samples (g.toMultiGraph hg) δ 3 (-1) hδ answers
    have he := randomCluster_coloring (g.toMultiGraph hg) 3
    norm_num only [Nat.cast_ofNat] at he
    rw [he] at hh
    simp only [Fintype.card_fin] at hh
    apply hh
    intro k hk l hl
    rw [ha k hk l hl,normalize_radialValue_parallel g hg δ (k+1) (l+1)]
    rfl

 theorem recoverThreeColoring_count (g : MixedCode) (hg : g.Valid 1 0)
    (δ : ℚ) (hδ : 1<δ) (answers : List ℚ)
    (ha : ∀ k<g.vertices,∀ l<g.edges.length+1,
      answers.getD (k*(g.edges.length+1)+l) 0=
        radialValue ((g.parallelLabel 0 (l+1)).toMultiGraph
          (MixedCode.parallelLabel_valid 0 (l+1) 1 0 g hg)) δ (k+1)) :
    recoverThreeColoring δ (g.vertices,(g.edges.length,answers))=
      (properColoringCount (g.toMultiGraph hg) 3 : ℚ) := by
  rw [recoverThreeColoring_radialAnswers g hg δ hδ answers ha,MultiGraph.unweighted,
    partition_eq_properColoringCount]
end PlanarHom.PottsTwoStageMachines
