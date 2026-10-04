import PlanarHom.FixedRealUnitDiagonalRigidity

/-! NEW general A.6/A.8 structural consequence for an actual weighted source
with nonzero, pairwise nonproportional numerical rows. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealNonproportionalClass
open DensePolynomial Complexity RepresentedBit FixedRealMixedInterpolation RelativeWeightedSpectralField
variable {n e q : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K] [Algebra K ℝ]

theorem class_of_not_hard (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (M : Matrix (Fin q) (Fin q) K) (w : Fin q → K)
    (hs : ∀ i j,M i j=M j i) (hnn : ∀ i j,0≤algebraMap K ℝ (M i j))
    (hw : ∀ i,0<algebraMap K ℝ (w i)) (hnz : ∀ i,realMatrix M i≠0)
    (hproj : ∀ i j,i≠j→∀t:ℝ,realMatrix M i≠t • realMatrix M j)
    (hn : ¬SharpPHard (problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) :
    Structures.NonnegativeClass (realMatrix M) := by
  by_contra hc
  have red := FixedRealWeightRemoval.removePositiveWeights basis (fun _ : Fin 1 => M)
    (fun l : Fin 0 => l.elim0) w 0 (fun i j => congrArg (algebraMap K ℝ) (hs i j)) hw hnz hproj
  exact hn ((FixedRealApproximation.theoremA6_hard basis (algebraMap K ℝ) M hs hnn hc).trans red)

variable {C : Type} [Fintype C]

theorem finite_class_of_not_hard (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (M : Matrix C C K) (w : C → K)
    (hs : ∀ i j,M i j=M j i) (hnn : ∀ i j,0≤algebraMap K ℝ (M i j))
    (hw : ∀ i,0<algebraMap K ℝ (w i)) (hnz : ∀ i,(fun j => algebraMap K ℝ (M i j))≠0)
    (hproj : ∀ i j,i≠j→∀t:ℝ,(fun k => algebraMap K ℝ (M i k))≠t • (fun k => algebraMap K ℝ (M j k)))
    (hn : ¬SharpPHard (FixedRealComponents.problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) :
    Structures.NonnegativeClass (fun i j => algebraMap K ℝ (M i j)) := by
  let f : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  have red := FixedRealActualTwins.reindexReduction basis M w f
  have hz : ∀ i,realMatrix (fun i j => M (f i) (f j)) i≠0 := by
    intro i he
    apply hnz (f i)
    funext j
    simpa only [realMatrix,Matrix.map,Matrix.of_apply,f.apply_symm_apply,Pi.zero_apply] using congrFun he (f.symm j)
  have hp : ∀ i j,i≠j→∀t:ℝ,realMatrix (fun i j => M (f i) (f j)) i≠t • realMatrix (fun i j => M (f i) (f j)) j := by
    intro i j hij t he
    apply hproj (f i) (f j) (fun h => hij (f.injective h)) t
    funext k
    simpa only [realMatrix,Matrix.map,Matrix.of_apply,f.apply_symm_apply,Pi.smul_apply] using congrFun he (f.symm k)
  have hc := class_of_not_hard basis (fun i j => M (f i) (f j)) (fun i => w (f i))
    (fun i j => hs _ _) (fun i j => hnn _ _) (fun i => hw _) hz hp (fun hh => hn (hh.trans red))
  have hh := hc.equiv f.symm
  simpa only [realMatrix,Matrix.map,Matrix.of_apply,f.apply_symm_apply] using hh

end PlanarHom.FixedRealNonproportionalClass
