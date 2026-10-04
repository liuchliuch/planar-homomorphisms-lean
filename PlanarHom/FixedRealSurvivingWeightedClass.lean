import PlanarHom.FixedRealWeightedTractability
import PlanarHom.FixedRealPrescribedZeroDeletion

/-! NEW exact A.13 deletion-before-quotient predicate and its full easy side.
The original source's positive-weight colors are selected first. Their actual
identical-row quotient, including its zero row, is then tested. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealSurvivingWeights
open DensePolynomial RepresentedBit Structures
variable {n e : ℕ} {K C : Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]

abbrev PositiveColors (φ : K →+* ℝ) (w : C → K) := {i // 0<φ (w i)}

def SurvivingClass (φ : K →+* ℝ) (M : Matrix C C K) (w : C → K) (hs : ∀ i j,M i j=M j i) : Prop :=
  PositiveVertexWeightClass (fun i j : PositiveColors φ w => φ (M i.val j.val))
    (fun i : PositiveColors φ w => φ (w i.val)) (fun i j => congrArg φ (hs i.val j.val))

theorem omitted_weight_zero (φ : K →+* ℝ) (w : C → K) (hw : ∀ i,0≤φ (w i)) :
    ∀ i,¬(0<φ (w i))→w i=0 := by
  intro i hi
  apply φ.injective
  rw [map_zero]
  exact le_antisymm (le_of_not_gt hi) (hw i)

theorem surviving_class_inFP (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix C C K) (w : C → K) (hs : ∀ i j,M i j=M j i)
    (hw : ∀ i,0≤φ (w i)) (h : SurvivingClass φ M w hs) :
    (FixedRealComponents.problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w).InFP := by
  have he := FixedRealGraphEvaluation.positiveVertexWeightClass_inFP basis φ
    (fun i j : PositiveColors φ w => M i.val j.val) (fun i : PositiveColors φ w => w i.val)
    (fun i j => hs _ _) h
  have red := FixedRealZeroWeights.deleteReduction basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w
    (fun i => 0<φ (w i)) (omitted_weight_zero φ w hw)
  have hu : (fun (l : Fin 0) (i : PositiveColors φ w) => (l.elim0 : C → K) i.val) =
      (fun l : Fin 0 => l.elim0) := by funext l; exact l.elim0
  rw [hu] at red
  exact red.inFP he

theorem surviving_class_zero_weights (φ : K →+* ℝ) (M : Matrix C C K) (w : C → K)
    (hs : ∀ i j,M i j=M j i) (hw : ∀ i,w i=0) : SurvivingClass φ M w hs := by
  letI : IsEmpty (PositiveColors φ w) := ⟨fun i => by
    have h := i.property
    rw [hw,map_zero] at h
    exact (lt_irrefl _ h)⟩
  unfold SurvivingClass PositiveVertexWeightClass WeightedClass
  refine ⟨0,(fun i => isEmptyElim i),?_,?_,?_⟩
  · intro r; exact r.elim0
  · intro i; exact isEmptyElim i
  · intro r; exact r.elim0

end PlanarHom.FixedRealSurvivingWeights
