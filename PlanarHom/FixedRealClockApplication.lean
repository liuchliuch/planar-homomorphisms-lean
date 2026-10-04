import PlanarHom.FixedRealPhysicalBoundary
import PlanarHom.ClockStructuralClassification
import PlanarHom.ClockLiteralFormula

/-! Corollary 12.5 in the exact fixed-real represented model, for both signs
of the coupling and every fixed positive microscopic weight vector. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealClock
open DensePolynomial RepresentedBit Structures FixedRealPhysicalModels
variable {d e q : ℕ} {F : Type} [Field F] [Algebra (RationalFunction d) F]

 theorem zero_coupling_inFP (basis : Module.Basis (Fin e) (RationalFunction d) F)
    (φ : F →+* ℝ) (M : Matrix (Fin q) (Fin q) F) (w : Fin q → F)
    (hM : ∀ i j,φ (M i j)=ClockModel.interaction q 0 i j) :
    (problem basis M w).InFP := by
  apply mapped_all_ones_inFP basis φ M w
  intro i j
  simpa only [ClockModel.zero_interaction] using hM i j

 theorem corollary125_nonzero (basis : Module.Basis (Fin e) (RationalFunction d) F)
    (φ : F →+* ℝ) (hq : 2≤q) (K : ℝ) (hK : K≠0)
    (M : Matrix (Fin q) (Fin q) F) (w : Fin q → F)
    (hM : ∀ i j,φ (M i j)=ClockModel.interaction q K i j) (hw : ∀ i,0<φ (w i)) :
    (((q=2 ∨ q=4) ∧ ∃ μ : ℝ,0<μ ∧ ∀ i,φ (w i)=μ) → (problem basis M w).InFP) ∧
    (¬((q=2 ∨ q=4) ∧ ∃ μ : ℝ,0<μ ∧ ∀ i,φ (w i)=μ) → SharpPHard (problem basis M w)) := by
  letI : Nonempty (Fin q) := ⟨⟨0,by omega⟩⟩
  have hs : ∀ i j,M i j=M j i := by
    intro i j
    apply φ.injective
    rw [hM,hM]
    exact ClockModel.symmetric q K i j
  have hp : ∀ i j,0<φ (M i j) := by
    intro i j
    rw [hM]
    exact ClockModel.positive q K i j
  have hm : (fun i j => φ (M i j))=ClockModel.interaction q K := funext (fun i => funext (hM i))
  have he : PositiveVertexWeightClass (fun i j => φ (M i j)) (fun i => φ (w i))
      (fun i j => congrArg φ (hs i j)) ↔
      (q=2 ∨ q=4) ∧ ∃ μ : ℝ,0<μ ∧ ∀ i,φ (w i)=μ := by
    simpa only [hm] using ClockModel.weighted_class_iff hq hK (fun i => φ (w i)) hw
  have hc := FixedRealPositiveWeightedClassification.dichotomy basis φ M hs hp w hw
  exact ⟨fun h => hc.1 (he.mpr h),fun h => hc.2 (fun hh => h (he.mp hh))⟩

/-- Complete zero/nonzero split in Corollary 12.5. -/
theorem corollary125 (basis : Module.Basis (Fin e) (RationalFunction d) F)
    (φ : F →+* ℝ) (hq : 2≤q) (K : ℝ)
    (M : Matrix (Fin q) (Fin q) F) (w : Fin q → F)
    (hM : ∀ i j,φ (M i j)=ClockModel.interaction q K i j) (hw : ∀ i,0<φ (w i)) :
    (K=0 → (problem basis M w).InFP) ∧
    (K≠0 →
      (((q=2 ∨ q=4) ∧ ∃ μ : ℝ,0<μ ∧ ∀ i,φ (w i)=μ) → (problem basis M w).InFP) ∧
      (¬((q=2 ∨ q=4) ∧ ∃ μ : ℝ,0<μ ∧ ∀ i,φ (w i)=μ) → SharpPHard (problem basis M w))) := by
  constructor
  · intro hK
    subst K
    exact zero_coupling_inFP basis φ M w hM
  · exact fun hK => corollary125_nonzero basis φ hq K hK M w hM hw

 theorem corollary125_unit (basis : Module.Basis (Fin e) (RationalFunction d) F)
    (φ : F →+* ℝ) (hq : 2≤q) (K : ℝ) (hK : K≠0)
    (M : Matrix (Fin q) (Fin q) F)
    (hM : ∀ i j,φ (M i j)=ClockModel.interaction q K i j) :
    ((q=2 ∨ q=4) → (problem basis M (fun _ => 1)).InFP) ∧
    ((q≠2 ∧ q≠4) → SharpPHard (problem basis M (fun _ => 1))) := by
  have hc := corollary125_nonzero basis φ hq K hK M (fun _ => 1) hM (fun _ => by simp)
  exact ⟨fun h => hc.1 ⟨h,1,zero_lt_one,fun _ => φ.map_one⟩,
    fun ⟨h2,h4⟩ => hc.2 (fun h => h.1.elim h2 h4)⟩

end PlanarHom.FixedRealClock
