import PlanarHom.FixedRealWeightedSupportSources
import PlanarHom.FixedRealWeightedTractability
import PlanarHom.InjectiveWeightedStructuralTransfer

/-! The full represented positive-interaction dichotomy. Actual identical rows
are aggregated first. This uses the proved positive-block necessity and does
not depend on the still separate rectangular/support assembly of A.12. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealPositiveWeightedClassification
open DensePolynomial RepresentedBit Structures FixedRealActualTwins
variable {n e : ℕ} {K C : Type} [Field K] [Algebra (RationalFunction n) K]
  [Fintype C] [Nonempty C]

 theorem class_of_not_hard (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix C C K) (hs : ∀ i j,M i j=M j i)
    (hp : ∀ i j,0<φ (M i j)) (w : C → K) (hw : ∀ i,0<φ (w i))
    (hn : ¬SharpPHard (FixedRealComponents.problem basis
      (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) :
    PositiveVertexWeightClass (fun i j => φ (M i j)) (fun i => φ (w i))
      (fun i j => congrArg φ (hs i j)) := by
  letI : Algebra K ℝ := φ.toAlgebra
  let Q := Twins.quotientMatrix M hs
  let v := Twins.quotientWeight M w
  letI : Nonempty (Quotient (Twins.rowSetoid M)) :=
    ⟨Quotient.mk _ (Classical.choice inferInstance)⟩
  have hqp : ∀ i j,0<algebraMap K ℝ (Q i j) := by
    intro i j
    induction i using Quotient.inductionOn with
    | h i => induction j using Quotient.inductionOn with
      | h j => exact hp i j
  have hwp : ∀ i,0<algebraMap K ℝ (v i) := quotientWeight_map_pos φ M w hw
  have hq := FixedRealWeightedSupportSources.positive_block_of_not_hard basis Q v
    (Twins.quotientMatrix_symmetric M hs) hqp (Twins.quotientMatrix_rows_injective M hs) hwp
    (fun h => hn (h.trans (quotientReduction basis M hs w)))
  have hc : WeightedClass (fun i j => φ (Q i j)) (fun i => φ (v i)) := hq.weightedClass
  apply WeightedClass.of_equiv (rowEquiv φ M)
  simpa only [←quotientMatrix_map φ M hs,←quotientWeight_map φ M w] using hc

 theorem dichotomy (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix C C K) (hs : ∀ i j,M i j=M j i)
    (hp : ∀ i j,0<φ (M i j)) (w : C → K) (hw : ∀ i,0<φ (w i)) :
    (PositiveVertexWeightClass (fun i j => φ (M i j)) (fun i => φ (w i))
      (fun i j => congrArg φ (hs i j)) →
      (FixedRealComponents.problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w).InFP) ∧
    (¬PositiveVertexWeightClass (fun i j => φ (M i j)) (fun i => φ (w i))
      (fun i j => congrArg φ (hs i j)) →
      SharpPHard (FixedRealComponents.problem basis
        (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w)) := by
  refine ⟨FixedRealGraphEvaluation.positiveVertexWeightClass_inFP basis φ M w hs,?_⟩
  intro hbad
  by_contra hn
  exact hbad (class_of_not_hard basis φ M hs hp w hw hn)

end PlanarHom.FixedRealPositiveWeightedClassification
