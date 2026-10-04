import PlanarHom.FixedRealPhysicalBoundary
import PlanarHom.CoupledIsingStructuralClassification
import PlanarHom.CoupledIsingUniformFibers
import PlanarHom.CoupledIsingSetSemantics

/-! Corollary 12.6 with exact fixed-real outputs and the literal character-map
fiber sums. Labels and couplings may have either sign; no transcendental entry
is assumed algebraic. Empty label families are included. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealCoupledIsing
open DensePolynomial RepresentedBit Structures FixedRealPhysicalModels BinaryCharacters
variable {d e n m : ℕ} {F : Type} [Field F] [Algebra (RationalFunction d) F]

 theorem corollary126 (basis : Module.Basis (Fin e) (RationalFunction d) F)
    (φ : F →+* ℝ) (a : Fin m → Space n) (ha : Function.Injective a)
    (hn : ∀ r,a r≠0) (J : Fin m → ℝ) (hJ : ∀ r,J r≠0)
    (M : Matrix (Space n) (Space n) F) (w : Space n → F)
    (hM : ∀ x y,φ (M x y)=CoupledIsing.interaction a J x y) (hw : ∀ x,0<φ (w x)) :
    ((LinearIndependent F₂ a ∧ ∃ μ : ℝ,0<μ ∧
        ∀ z,CoupledIsing.aggregatedWeight a (fun x => φ (w x)) z=μ) → (problem basis M w).InFP) ∧
    (¬(LinearIndependent F₂ a ∧ ∃ μ : ℝ,0<μ ∧
        ∀ z,CoupledIsing.aggregatedWeight a (fun x => φ (w x)) z=μ) → SharpPHard (problem basis M w)) := by
  have hs : ∀ x y,M x y=M y x := by
    intro x y
    apply φ.injective
    rw [hM,hM]
    exact CoupledIsing.symmetric a J x y
  have hp : ∀ x y,0<φ (M x y) := by
    intro x y
    rw [hM]
    exact Real.exp_pos _
  have hm : (fun x y => φ (M x y))=CoupledIsing.interaction a J := funext (fun x => funext (hM x))
  have he : PositiveVertexWeightClass (fun x y => φ (M x y)) (fun x => φ (w x))
      (fun x y => congrArg φ (hs x y)) ↔
      LinearIndependent F₂ a ∧ ∃ μ : ℝ,0<μ ∧
        ∀ z,CoupledIsing.aggregatedWeight a (fun x => φ (w x)) z=μ := by
    simpa only [hm] using CoupledIsing.weighted_class_iff a ha hn J hJ (fun x => φ (w x)) hw
  have hc := FixedRealPositiveWeightedClassification.dichotomy basis φ M hs hp w hw
  exact ⟨fun h => hc.1 (he.mpr h),fun h => hc.2 (fun hh => h (he.mp hh))⟩

 theorem corollary126_unit (basis : Module.Basis (Fin e) (RationalFunction d) F)
    (φ : F →+* ℝ) (a : Fin m → Space n) (ha : Function.Injective a)
    (hn : ∀ r,a r≠0) (J : Fin m → ℝ) (hJ : ∀ r,J r≠0)
    (M : Matrix (Space n) (Space n) F)
    (hM : ∀ x y,φ (M x y)=CoupledIsing.interaction a J x y) :
    (LinearIndependent F₂ a → (problem basis M (fun _ => 1)).InFP) ∧
    (¬LinearIndependent F₂ a → SharpPHard (problem basis M (fun _ => 1))) := by
  have hc := corollary126 basis φ a ha hn J hJ M (fun _ => 1) hM (fun _ => by simp)
  constructor
  · intro hi
    apply hc.1
    refine ⟨hi,(2 : ℝ)^(n-Matrix.rank a),by positivity,?_⟩
    intro z
    simpa only [map_one] using CoupledIsing.unit_aggregatedWeight a z
  · intro hi
    exact hc.2 (fun h => hi h.1)

/-- The paper's finite-set formulation, with its actual image fibers. -/
theorem corollary126_set (basis : Module.Basis (Fin e) (RationalFunction d) F)
    (φ : F →+* ℝ) (A : Finset (Space n)) (hA : (0 : Space n)∉A)
    (J : Space n → ℝ) (hJ : ∀ a∈A,J a≠0)
    (M : Matrix (Space n) (Space n) F) (w : Space n → F)
    (hM : ∀ x y,φ (M x y)=CoupledIsing.interaction (CoupledIsing.setLabels A)
      (CoupledIsing.setCouplings A J) x y) (hw : ∀ x,0<φ (w x)) :
    ((LinearIndependent F₂ (fun a : ↥A => a.val) ∧ ∃ μ : ℝ,0<μ ∧
        ∀ z,CoupledIsing.aggregatedWeight (CoupledIsing.setLabels A) (fun x => φ (w x)) z=μ) →
      (problem basis M w).InFP) ∧
    (¬(LinearIndependent F₂ (fun a : ↥A => a.val) ∧ ∃ μ : ℝ,0<μ ∧
        ∀ z,CoupledIsing.aggregatedWeight (CoupledIsing.setLabels A) (fun x => φ (w x)) z=μ) →
      SharpPHard (problem basis M w)) := by
  have hc := corollary126 basis φ (CoupledIsing.setLabels A) (CoupledIsing.setLabels_injective A)
    (CoupledIsing.setLabels_nonzero A hA) (CoupledIsing.setCouplings A J)
    (fun r => hJ _ ((Fintype.equivFin ↥A).symm r).property) M w hM hw
  simpa only [CoupledIsing.setLabels_independent_iff] using hc

 theorem corollary126_set_unit (basis : Module.Basis (Fin e) (RationalFunction d) F)
    (φ : F →+* ℝ) (A : Finset (Space n)) (hA : (0 : Space n)∉A)
    (J : Space n → ℝ) (hJ : ∀ a∈A,J a≠0)
    (M : Matrix (Space n) (Space n) F)
    (hM : ∀ x y,φ (M x y)=CoupledIsing.interaction (CoupledIsing.setLabels A)
      (CoupledIsing.setCouplings A J) x y) :
    (LinearIndependent F₂ (fun a : ↥A => a.val) → (problem basis M (fun _ => 1)).InFP) ∧
    (¬LinearIndependent F₂ (fun a : ↥A => a.val) → SharpPHard (problem basis M (fun _ => 1))) := by
  have hc := corollary126_unit basis φ (CoupledIsing.setLabels A) (CoupledIsing.setLabels_injective A)
    (CoupledIsing.setLabels_nonzero A hA) (CoupledIsing.setCouplings A J)
    (fun r => hJ _ ((Fintype.equivFin ↥A).symm r).property) M hM
  simpa only [CoupledIsing.setLabels_independent_iff] using hc

 theorem empty_labels_inFP (basis : Module.Basis (Fin e) (RationalFunction d) F)
    (φ : F →+* ℝ) (a : Fin 0 → Space n) (J : Fin 0 → ℝ)
    (M : Matrix (Space n) (Space n) F) (w : Space n → F)
    (hM : ∀ x y,φ (M x y)=CoupledIsing.interaction a J x y) :
    (problem basis M w).InFP := by
  apply mapped_all_ones_inFP basis φ M w
  intro x y
  simpa only [PhysicalModels.coupled_empty_interaction] using hM x y

end PlanarHom.FixedRealCoupledIsing
