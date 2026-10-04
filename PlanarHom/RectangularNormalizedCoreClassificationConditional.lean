-- NEW conditional assembly adapted from the exact recovered normalized-core consumer.
-- Explicit classifier hypotheses are instantiated by the closed assembly.
import PlanarHom.RectangularUnitCoreSource
import PlanarHom.RectangularCoreSourceRigidityConditional

/-! Actual source non-hardness classifies the literal real, background-weighted
normalized rectangular core. The finite indices used by the source program are
transported back to the original row and column quotients. Neither a classifier
nor a source-availability assumption occurs in the conclusion's hypotheses. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularNormalizedCoreClassification
open Boolean RectangularTwinQuotient RectangularWeightedNormNormalization
open RectangularUnitCoreSource
open RectangularSourceNormSimulation (block realRectangular)
open RectangularBackgroundSourceNormSimulation (weights)
open Complexity Complexity.MixedCode AlgebraicProductInterpolation

variable {p s n : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)]
variable {K₀ : IntermediateField ℚ ℝ}

/-- The true Lemma 9.2 endpoint applied to the actual unit-core source program.
Original repeated or proportional rows and columns are allowed. The two
quotients are the literal quotients of the original weighted normalization. -/
theorem source_core_tensor_of_potts
    (hPotts : AlgebraicProductInterpolation.RealLanguage.PositivePottsFoundation)
    (basis : Module.Basis (Fin n) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j,0<(V i j:ℝ))
    (μ : Fin p→K₀) (ν : Fin s→K₀) (hμ : ∀ i,0<(μ i:ℝ)) (hν : ∀ j,0<(ν j:ℝ))
    (hnot : ¬PromisedSharpPHard
      (evaluationProblem basis (fun _:Fin 1=>block V) (fun l:Fin 0=>l.elim0) (weights μ ν))) :
    ∃ d : ℕ,
    ∃ eR : Rows (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)))≃Cube d,
    ∃ eC : Columns (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)))≃Cube d,
    ∃ γ : ℝ,∃ ρ : Fin d→ℝ,0<γ ∧ (∀ i,0<ρ i ∧ ρ i<1) ∧
      ∀ r c,core (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))) r c=
        γ*tensor ρ (eR r) (eC c) := by
  let N := normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))
  letI : Nonempty (Fin (Fintype.card (Rows N))) := Fin.pos_iff_nonempty.mp (row_card_pos N)
  letI : Nonempty (Fin (Fintype.card (Columns N))) := Fin.pos_iff_nonempty.mp (column_card_pos N)
  obtain ⟨U,hunit,hM,⟨red⟩⟩ := exists_unit_core_language basis V hV μ ν hμ hν
  have hN : ∀ i j,0<N i j := normalized_pos _ hV _ _ hμ hν
  have hrows : ∀ i j,i≠j→∀ t:ℝ,finCore N i≠t•finCore N j := by
    intro i j hij t h
    apply hij
    exact (finCore_no_proportional_rows _ hV _ _ hμ hν i j t (fun k=>by
      simpa only [Pi.smul_apply,smul_eq_mul] using congrFun h k)).2
  have hcolumns : ∀ i j,i≠j→∀ t:ℝ,(finCore N).transpose i≠t•(finCore N).transpose j := by
    intro i j hij t h
    apply hij
    exact (finCore_no_proportional_columns _ hV _ _ hμ hν i j t (fun k=>by
      simpa only [Matrix.transpose_apply,Pi.smul_apply,smul_eq_mul] using congrFun h k)).2
  have hn : ¬PromisedSharpPHard U.problem := fun hh=>hnot (hh.trans red)
  obtain ⟨d,eX,eY,γ,ρ,hγ,hρ,hcore⟩ :=
    RectangularCoreSourceRigidity.rectangular_tensor_of_source_of_potts hPotts U hunit
      (finCore N) (finCore_positive N hN) hM hrows hcolumns hn
  refine ⟨d,(rowIndex N).symm.trans eX,(columnIndex N).symm.trans eY,γ,ρ,hγ,hρ,?_⟩
  intro r c
  simpa only [finCore,Equiv.apply_symm_apply,Equiv.trans_apply] using
    hcore ((rowIndex N).symm r) ((columnIndex N).symm c)

/-- Unit backgrounds retain the original unweighted source codec and need no
injectivity of its original rows or columns. -/
theorem source_unit_core_tensor_of_potts
    (hPotts : AlgebraicProductInterpolation.RealLanguage.PositivePottsFoundation)
    (basis : Module.Basis (Fin n) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j,0<(V i j:ℝ))
    (hnot : ¬PromisedSharpPHard
      (evaluationProblem basis (fun _:Fin 1=>block V) (fun l:Fin 0=>l.elim0) (fun _=>1))) :
    ∃ d : ℕ,
    ∃ eR : Rows (normalized (realRectangular V) (fun _=>1) (fun _=>1))≃Cube d,
    ∃ eC : Columns (normalized (realRectangular V) (fun _=>1) (fun _=>1))≃Cube d,
    ∃ γ : ℝ,∃ ρ : Fin d→ℝ,0<γ ∧ (∀ i,0<ρ i ∧ ρ i<1) ∧
      ∀ r c,core (normalized (realRectangular V) (fun _=>1) (fun _=>1)) r c=
        γ*tensor ρ (eR r) (eC c) := by
  have hw : weights (fun _:Fin p=>(1:K₀)) (fun _:Fin s=>(1:K₀))=(fun _=>1) := by
    funext i
    refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;> simp [weights]
  exact source_core_tensor_of_potts hPotts basis V hV (fun _=>1) (fun _=>1)
    (fun _=>zero_lt_one) (fun _=>zero_lt_one) (by simpa only [hw] using hnot)

end PlanarHom.RectangularNormalizedCoreClassification
