import PlanarHom.FixedRealWeightedSupportSources
import PlanarHom.FixedRealSupportDichotomy
import PlanarHom.NonnegativeSupportShapesBasic

/-! NEW support assembly for A.12. The rectangular necessity theorem is an
explicit internal argument here, discharged by the genuine normalized moment
proof in FixedRealWeightedNecessity. -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical
namespace PlanarHom.FixedRealWeightedSupportAssembly
open DensePolynomial Complexity RepresentedBit RootedRestriction NonnegativeSupportShapes Structures
open RectangularSourceNormSimulation RectangularBackgroundSourceNormSimulation
variable {n e q : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K] [Algebra K ℝ]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

theorem shapes_of_not_hard (M : Matrix (Fin q) (Fin q) K) (hs : ∀ i j,M i j=M j i)
    (hnn : ∀ i j,0≤algebraMap K ℝ (M i j)) (w : Fin q → K)
    (hw : ∀ i,0<algebraMap K ℝ (w i))
    (hn : ¬SharpPHard (FixedRealComponents.problem basis
      (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) :
    ∀ c : (colorSupport (fun i j => algebraMap K ℝ (M i j))
      (fun i j => congrArg (algebraMap K ℝ) (hs i j))).ConnectedComponent,
      Shape (fun i j : c.supp => algebraMap K ℝ (M i.val j.val)) := by
  intro c
  apply shape_of_basic_support _ (fun i j => congrArg (algebraMap K ℝ) (hs _ _)) (fun i j => hnn _ _)
  by_contra hc
  exact hn (FixedRealSupportHardness.theoremA9_hard basis (algebraMap K ℝ) M hs w hw ⟨c,hc⟩)

theorem weightedClass_of_rectangular
    (hrect : ∀ {p s : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)],
      ∀ (V : Matrix (Fin p) (Fin s) K) (μ : Fin p → K) (ν : Fin s → K),
      (∀ i j,0<algebraMap K ℝ (V i j)) →
      Function.Injective (block V) →
      (∀ i,0<algebraMap K ℝ (μ i)) → (∀ i,0<algebraMap K ℝ (ν i)) →
      ¬SharpPHard (FixedRealComponents.problem basis (fun _ : Fin 1 => block V)
        (fun l : Fin 0 => l.elim0) (weights μ ν)) →
      AllowedWeightedBlock (fun i j => algebraMap K ℝ (block V i j))
        (fun i => algebraMap K ℝ (weights μ ν i)))
    (M : Matrix (Fin q) (Fin q) K) (hs : ∀ i j,M i j=M j i)
    (hnn : ∀ i j,0≤algebraMap K ℝ (M i j)) (hi : Function.Injective M)
    (w : Fin q → K) (hw : ∀ i,0<algebraMap K ℝ (w i))
    (hn : ¬SharpPHard (FixedRealComponents.problem basis
      (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) :
    WeightedClass (fun i j => algebraMap K ℝ (M i j)) (fun i => algebraMap K ℝ (w i)) := by
  apply weightedClass_of_supportBlocks _ _ (fun i j => congrArg (algebraMap K ℝ) (hs i j))
  intro c
  letI : DecidablePred (fun i => i ∈ c.supp) := fun _ => Classical.propDecidable _
  letI : Nonempty c.supp := by obtain ⟨i,hi⟩ := c.nonempty_supp; exact ⟨⟨i,hi⟩⟩
  have hX : ColorClosed M c.supp := by
    intro i hi j hj
    exact component_colorClosed (fun i j => algebraMap K ℝ (M i j))
      (fun i j => congrArg (algebraMap K ℝ) (hs i j)) c i hi j ((map_ne_zero (algebraMap K ℝ)).mpr hj)
  have red := FixedRealWeightedSupportSources.submatrixReduction basis M hs w hw c.supp hX
  have hcnot : ¬SharpPHard (FixedRealComponents.problem basis
      (fun _ : Fin 1 => fun i j : c.supp => M i.val j.val) (fun l : Fin 0 => l.elim0)
      (fun i : c.supp => w i.val)) := fun h => hn (h.trans red)
  have hci := FixedRealWeightedSupportSources.submatrix_rows_injective M hi c.supp hX
  have shape := shapes_of_not_hard basis M hs hnn w hw hn c
  cases shape with
  | zero a hm => exact .zero a (fun i j => congrFun (congrFun hm i) j) (fun i => hw _)
  | positive hp =>
    exact FixedRealWeightedSupportSources.positive_block_of_not_hard basis
      (fun i j : c.supp => M i.val j.val) (fun i : c.supp => w i.val)
      (fun i j => hs _ _) hp hci (fun i => hw _) hcnot
  | bipartite p s hp hspos a VR hVR hM =>
    letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
    letI : Nonempty (Fin s) := ⟨⟨0,hspos⟩⟩
    let g : Fin (p+s) ≃ c.supp := finSumFinEquiv.symm.trans a.symm
    let V : Matrix (Fin p) (Fin s) K := fun i j => M (g (Fin.castAdd s i)).val (g (Fin.natAdd p j)).val
    let μ : Fin p → K := fun i => w (g (Fin.castAdd s i)).val
    let ν : Fin s → K := fun j => w (g (Fin.natAdd p j)).val
    have hreal : ∀ i j,algebraMap K ℝ (M (g i).val (g j).val)=block VR i j := by
      intro i j
      have hh := congrFun (congrFun hM (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
      change algebraMap K ℝ (M (g i).val (g j).val) =
        NonnegativeSupportShapes.double VR (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) at hh
      rw [hh]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [NonnegativeSupportShapes.double,block]
    have hV : ∀ i j,algebraMap K ℝ (V i j)=VR i j := by
      intro i j
      exact (hreal (Fin.castAdd s i) (Fin.natAdd p j)).trans (block_left_right VR i j)
    have hblock : (fun i j => M (g i).val (g j).val)=block V := by
      funext i j
      apply (algebraMap K ℝ).injective
      rw [hreal]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp only [block_left_left,block_left_right,block_right_left,block_right_right,map_zero,hV]
    have hweight : (fun i => w (g i).val)=weights μ ν := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;>
        simp only [weights,Fin.addCases_left,Fin.addCases_right,μ,ν]
    have hr := FixedRealActualTwins.reindexReduction basis (fun i j : c.supp => M i.val j.val)
      (fun i : c.supp => w i.val) g
    rw [hblock,hweight] at hr
    have hib : Function.Injective (block V) := by
      rw [←hblock]
      intro i j hij
      apply g.injective
      apply hci
      funext k
      simpa only [g.apply_symm_apply] using congrFun hij (g.symm k)
    have hb := hrect V μ ν (fun i j => by rw [hV];exact hVR i j) hib
      (fun i => hw _) (fun j => hw _) (fun h => hcnot (h.trans hr))
    rw [←hblock,←hweight] at hb
    exact AllowedWeightedBlock.of_equiv g hb

end PlanarHom.FixedRealWeightedSupportAssembly
