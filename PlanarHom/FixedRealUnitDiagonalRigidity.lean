import PlanarHom.PositiveClassUnitTensor
import PlanarHom.FixedRealActualTwins
import PlanarHom.FixedRealLemmaA10
import PlanarHom.RealNonnegativeHardness
import PlanarHom.FixedRealPositiveWeightRemoval
import PlanarHom.Normalization

/-! NEW represented unit-diagonal rigidity. Actual positive-background removal
and A.6 force the pure tensor form; its parameters are original source entries.
A.10 then forces the original core weights to be constant. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealUnitDiagonalRigidity
open DensePolynomial Complexity Complexity.MixedCode RepresentedBit Boolean
open FixedRealMixedInterpolation RelativeWeightedSpectralField
variable {n e q : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K] [Algebra K ℝ]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

theorem class_of_not_hard (M : Matrix (Fin q) (Fin q) K) (w : Fin q → K)
    (hs : ∀ i j, M i j = M j i)
    (hp : ∀ i j, 0 < algebraMap K ℝ (M i j))
    (hd : ∀ i, algebraMap K ℝ (M i i) = 1)
    (hi : Function.Injective M) (hw : ∀ i, 0 < algebraMap K ℝ (w i))
    (hn : ¬SharpPHard (problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) :
    Structures.NonnegativeClass (fun i j => algebraMap K ℝ (M i j)) := by
  by_contra hc
  have hri : Function.Injective (fun i j => algebraMap K ℝ (M i j)) := by
    intro i j he
    apply hi
    funext k
    exact (algebraMap K ℝ).injective (congrFun he k)
  have hrs : ∀ i j, algebraMap K ℝ (M i j) = algebraMap K ℝ (M j i) :=
    fun i j => congrArg (algebraMap K ℝ) (hs i j)
  have hproj := positive_unitDiagonal_rows_nonproportional
    (fun i j => algebraMap K ℝ (M i j)) hp hrs hd hri
  have hnz : ∀ i, realMatrix M i ≠ 0 := by
    intro i h
    exact (ne_of_gt (hp i i)) (congrFun h i)
  have remove := FixedRealWeightRemoval.removePositiveWeights basis (fun _ : Fin 1 => M)
    (fun l : Fin 0 => l.elim0) w 0 hrs hw hnz hproj
  exact hn ((FixedRealApproximation.theoremA6_hard basis (algebraMap K ℝ) M hs
    (fun i j => (hp i j).le) hc).trans remove)

variable [Nonempty (Fin q)]

theorem tensor_of_not_hard (M : Matrix (Fin q) (Fin q) K) (w : Fin q → K)
    (hs : ∀ i j, M i j = M j i)
    (hp : ∀ i j, 0 < algebraMap K ℝ (M i j))
    (hd : ∀ i, algebraMap K ℝ (M i i) = 1)
    (hi : Function.Injective M) (hw : ∀ i, 0 < algebraMap K ℝ (w i))
    (hn : ¬SharpPHard (problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) :
    ∃ d : ℕ, ∃ a : Fin q ≃ Cube d, ∃ ρ : Fin d → K,
      (∀ r, 0 < algebraMap K ℝ (ρ r) ∧ algebraMap K ℝ (ρ r) ≠ 1) ∧
      ∀ i j, M i j = FixedRealTensorCoreEasy.tensor ρ (a i) (a j) := by
  have hri : Function.Injective (fun i j => algebraMap K ℝ (M i j)) := by
    intro i j he
    apply hi
    funext k
    exact (algebraMap K ℝ).injective (congrFun he k)
  obtain ⟨d,a,ρ,hρ,hm⟩ := PositiveClassUnitTensor.tensor_of_class
    (fun i j => algebraMap K ℝ (M i j)) hp hd hri (class_of_not_hard basis M w hs hp hd hi hw hn)
  let p : Fin d → K := fun r => M (a.symm (fun _ => false)) (a.symm (unitBit r))
  have hpr : ∀ r, algebraMap K ℝ (p r) = ρ r := by
    intro r
    simpa only [p,a.apply_symm_apply,tensor_unitBit] using
      hm (a.symm (fun _ => false)) (a.symm (unitBit r))
  refine ⟨d,a,p,(fun r => by simpa only [hpr] using hρ r),?_⟩
  intro i j
  apply (algebraMap K ℝ).injective
  rw [FixedRealLemmaA10.tensor_real]
  simpa only [hpr] using hm i j

theorem weights_constant (M : Matrix (Fin q) (Fin q) K) (w : Fin q → K)
    (hs : ∀ i j, M i j = M j i)
    (hp : ∀ i j, 0 < algebraMap K ℝ (M i j))
    (hd : ∀ i, algebraMap K ℝ (M i i) = 1)
    (hi : Function.Injective M) (hw : ∀ i, 0 < algebraMap K ℝ (w i))
    (hn : ¬SharpPHard (problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) :
    ∀ i j, w i = w j := by
  obtain ⟨d,a,ρ,hρ,hm⟩ := tensor_of_not_hard basis M w hs hp hd hi hw hn
  let u : Cube d → K := fun x => w (a.symm x)
  have red := FixedRealActualTwins.reindexReduction basis M w a.symm
  have he : (fun i j => M (a.symm i) (a.symm j)) = FixedRealTensorCoreEasy.tensor ρ := by
    funext i j
    simp only [hm,a.apply_symm_apply]
  rw [he] at red
  intro i j
  by_contra hij
  have hard := FixedRealLemmaA10.tensor_nonconstant_hard basis ρ (fun r => (hρ r).1)
    (fun r => (hρ r).2) u (fun x => hw (a.symm x))
    ⟨a i,a j,by simpa only [u,a.symm_apply_apply] using hij⟩
  exact hn (hard.trans red)

end PlanarHom.FixedRealUnitDiagonalRigidity
