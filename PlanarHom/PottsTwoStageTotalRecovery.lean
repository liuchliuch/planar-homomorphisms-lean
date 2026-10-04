import PlanarHom.PottsTwoStageRadialRecovery
import PlanarHom.NatListSumMachines
import PlanarHom.ConditionalMachines

/-! The real two-stage recovery includes the empty source graph explicitly.
All nonempty inputs use the existing exact radial interpolation program. -/
noncomputable section
open Classical
namespace PlanarHom.PottsTwoStageMachines
open Complexity PairProjectionMachines MultiGraph PottsTwoStageInterpolation

 def recoverThreeState (δ : ℚ) (p : Input) : ℚ := if p.1=0 then 1 else recover δ 3 1 p

 theorem fp_recoverThreeState (δ : ℚ) : FP inputEncoding fieldCode (recoverThreeState δ) := by
  have hn := (fp_fst BitEncoding.unaryNat (BitEncoding.unaryNat.prod fieldCode.list)).comp
    UnaryNatConversionMachine.fp_conversion
  have hz := (hn.pair (fp_const inputEncoding BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  exact (hz.ite (fp_const inputEncoding fieldCode (1:ℚ)) (fp_recover δ 3 1)).congr
    (fun _ => by simp [recoverThreeState])

 theorem unweighted_empty_source {V E : Type} [Fintype V] [Fintype E] [IsEmpty V]
    (G : MultiGraph V E) {C : Type} [Fintype C] (M : Matrix C C ℚ) : G.unweighted M=1 := by
  letI : IsEmpty E := ⟨fun e => isEmptyElim (G.src e)⟩
  rw [unweighted_eq]
  simp

 theorem recoverThreeState_radialAnswers (g : MixedCode) (hg : g.Valid 1 0)
    (δ : ℚ) (hδ : 1<δ) (answers : List ℚ)
    (ha : ∀ k<g.vertices,∀ l<g.edges.length+1,
      answers.getD (k*(g.edges.length+1)+l) 0=
        radialValue ((g.parallelLabel 0 (l+1)).toMultiGraph
          (MixedCode.parallelLabel_valid 0 (l+1) 1 0 g hg)) δ (k+1)) :
    recoverThreeState δ (g.vertices,(g.edges.length,answers))=
      (g.toMultiGraph hg).unweighted (ProperColoringPottsReduction.positivePottsMatrix 3) := by
  by_cases hn : g.vertices=0
  · letI : IsEmpty (Fin g.vertices) := by rw [hn]; infer_instance
    simp only [recoverThreeState,hn,ite_true]
    exact (unweighted_empty_source _ _).symm
  · letI : Nonempty (Fin g.vertices) := ⟨⟨0,Nat.pos_of_ne_zero hn⟩⟩
    rw [recoverThreeState,if_neg hn]
    exact recover_threeState_radialAnswers g hg δ hδ answers ha
end PlanarHom.PottsTwoStageMachines
