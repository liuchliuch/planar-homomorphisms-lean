import PlanarHom.FixedRealUnitDiagonalRigidity

/-! NEW arbitrary finite-color interface for actual normalized row quotients.
Finite indexing is performed by an exact unchanged-graph color reduction. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealUnitDiagonalRigidity
open DensePolynomial Complexity RepresentedBit Boolean
variable {n e : ℕ} {K C : Type} [Field K] [Algebra (RationalFunction n) K] [Algebra K ℝ]
  [Fintype C] [Nonempty C]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

theorem finite_tensor_of_not_hard (M : Matrix C C K) (w : C → K)
    (hs : ∀ i j, M i j = M j i) (hp : ∀ i j, 0 < algebraMap K ℝ (M i j))
    (hd : ∀ i, algebraMap K ℝ (M i i) = 1) (hi : Function.Injective M)
    (hw : ∀ i, 0 < algebraMap K ℝ (w i))
    (hn : ¬SharpPHard (FixedRealComponents.problem basis
      (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) :
    ∃ d : ℕ, ∃ a : C ≃ Cube d, ∃ ρ : Fin d → K,
      (∀ r, 0 < algebraMap K ℝ (ρ r) ∧ algebraMap K ℝ (ρ r) ≠ 1) ∧
      ∀ i j, M i j = FixedRealTensorCoreEasy.tensor ρ (a i) (a j) := by
  let f : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  letI : Nonempty (Fin (Fintype.card C)) := ⟨f.symm (Classical.choice inferInstance)⟩
  have hr := FixedRealActualTwins.reindexReduction basis M w f
  have hfi : Function.Injective (fun i j => M (f i) (f j)) := by
    intro i j hij
    apply f.injective
    apply hi
    funext k
    simpa only [f.apply_symm_apply] using congrFun hij (f.symm k)
  obtain ⟨d,a,ρ,hρ,hm⟩ := tensor_of_not_hard basis (fun i j => M (f i) (f j))
    (fun i => w (f i)) (fun i j => hs _ _) (fun i j => hp _ _) (fun i => hd _)
    hfi (fun i => hw _) (fun hh => hn (hh.trans hr))
  refine ⟨d,f.symm.trans a,ρ,hρ,?_⟩
  intro i j
  simpa only [f.apply_symm_apply,Equiv.trans_apply] using hm (f.symm i) (f.symm j)

theorem finite_weights_constant (M : Matrix C C K) (w : C → K)
    (hs : ∀ i j, M i j = M j i) (hp : ∀ i j, 0 < algebraMap K ℝ (M i j))
    (hd : ∀ i, algebraMap K ℝ (M i i) = 1) (hi : Function.Injective M)
    (hw : ∀ i, 0 < algebraMap K ℝ (w i))
    (hn : ¬SharpPHard (FixedRealComponents.problem basis
      (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) :
    ∀ i j, w i = w j := by
  let f : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  letI : Nonempty (Fin (Fintype.card C)) := ⟨f.symm (Classical.choice inferInstance)⟩
  have hr := FixedRealActualTwins.reindexReduction basis M w f
  have hfi : Function.Injective (fun i j => M (f i) (f j)) := by
    intro i j hij
    apply f.injective
    apply hi
    funext k
    simpa only [f.apply_symm_apply] using congrFun hij (f.symm k)
  have he := weights_constant basis (fun i j => M (f i) (f j))
    (fun i => w (f i)) (fun i j => hs _ _) (fun i j => hp _ _) (fun i => hd _)
    hfi (fun i => hw _) (fun hh => hn (hh.trans hr))
  intro i j
  simpa only [f.apply_symm_apply] using he (f.symm i) (f.symm j)

end PlanarHom.FixedRealUnitDiagonalRigidity
