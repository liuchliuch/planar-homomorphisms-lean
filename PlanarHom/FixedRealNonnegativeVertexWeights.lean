import PlanarHom.FixedRealWeightedClassification
import PlanarHom.FixedRealSurvivingWeightedClass
import PlanarHom.PhysicalWeightedReindex

/-! A.13 final assembly from the genuine full A.12 theorem.
Zero weights are deleted before the actual numerical row quotient. Exact
smaller-field deletion/restoration is supplied by FixedRealPrescribedZeroDeletion. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealSurvivingWeights
open DensePolynomial RepresentedBit Structures FixedRealMixedInterpolation
variable {n e q : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]

theorem theoremA13 (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix (Fin q) (Fin q) K) (hs : ∀ i j,M i j=M j i)
    (hnn : ∀ i j,0≤φ (M i j)) (w : Fin q → K) (hw : ∀ i,0≤φ (w i)) :
    (SurvivingClass φ M w hs → (problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w).InFP) ∧
    (¬SurvivingClass φ M w hs → SharpPHard (problem basis
      (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) := by
  refine ⟨surviving_class_inFP basis φ M w hs hw,?_⟩
  intro hbad
  let S := PositiveColors φ w
  let f : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let N : Matrix (Fin (Fintype.card S)) (Fin (Fintype.card S)) K := fun i j => M (f i).val (f j).val
  let v := fun i => w (f i).val
  have hsN : ∀ i j,N i j=N j i := fun i j => hs _ _
  have hclass : ¬PositiveVertexWeightClass (fun i j => φ (N i j)) (fun i => φ (v i))
      (fun i j => congrArg φ (hsN i j)) := by
    intro h
    apply hbad
    exact (positiveVertexWeightClass_reindex_iff
      (fun i j : S => φ (M i.val j.val)) (fun i : S => φ (w i.val))
      (fun i j => congrArg φ (hs i.val j.val)) f).mp h
  have hard := (FixedRealWeightedClassification.theoremA12 basis φ N hsN
    (fun i j => hnn _ _) v (fun i => (f i).property)).2 hclass
  have ri := FixedRealActualTwins.reindexReduction basis (fun i j : S => M i.val j.val)
    (fun i : S => w i.val) f
  have rr := FixedRealZeroWeights.restoreReduction basis (fun _ : Fin 1 => M)
    (fun l : Fin 0 => l.elim0) w (fun i => 0<φ (w i)) (omitted_weight_zero φ w hw)
  have hu : (fun (l : Fin 0) (i : PositiveColors φ w) => (l.elim0 : Fin q → K) i.val) =
      (fun l : Fin 0 => l.elim0) := by funext l; exact l.elim0
  rw [hu] at rr
  exact (hard.trans ri).trans rr

end PlanarHom.FixedRealSurvivingWeights
