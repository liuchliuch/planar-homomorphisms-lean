import PlanarHom.FixedRealPhysicalBoundary
import PlanarHom.BlumeCapelMatrix

/-! Corollary 12.7 for every finite real coupling, crystal field, and magnetic
field, in the original prescribed exact representation. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealBlumeCapel
open DensePolynomial RepresentedBit Structures FixedRealPhysicalModels
variable {d e : ℕ} {F : Type} [Field F] [Algebra (RationalFunction d) F]

 theorem zero_coupling_inFP (basis : Module.Basis (Fin e) (RationalFunction d) F)
    (φ : F →+* ℝ) (M : Matrix (Fin 3) (Fin 3) F) (w : Fin 3 → F)
    (hM : ∀ i j,φ (M i j)=BlumeCapel.interaction 0 i j) :
    (problem basis M w).InFP := by
  apply mapped_all_ones_inFP basis φ M w
  intro i j
  simpa only [BlumeCapel.zero_interaction] using hM i j

 theorem nonzero_coupling_hard (basis : Module.Basis (Fin e) (RationalFunction d) F)
    (φ : F →+* ℝ) (K : ℝ) (hK : K≠0)
    (M : Matrix (Fin 3) (Fin 3) F) (w : Fin 3 → F)
    (hM : ∀ i j,φ (M i j)=BlumeCapel.interaction K i j) (hw : ∀ i,0<φ (w i)) :
    SharpPHard (problem basis M w) := by
  have hs : ∀ i j,M i j=M j i := by
    intro i j
    apply φ.injective
    rw [hM,hM]
    exact BlumeCapel.symmetric K i j
  have hp : ∀ i j,0<φ (M i j) := by
    intro i j
    rw [hM]
    exact BlumeCapel.positive K i j
  have hm : (fun i j => φ (M i j))=BlumeCapel.interaction K := funext (fun i => funext (hM i))
  apply (FixedRealPositiveWeightedClassification.dichotomy basis φ M hs hp w hw).2
  intro hh
  apply BlumeCapel.not_weighted_class hK (fun i => φ (w i))
  simpa only [hm] using hh

 theorem corollary127 (basis : Module.Basis (Fin e) (RationalFunction d) F)
    (φ : F →+* ℝ) (K D H : ℝ)
    (M : Matrix (Fin 3) (Fin 3) F) (w : Fin 3 → F)
    (hM : ∀ i j,φ (M i j)=BlumeCapel.interaction K i j)
    (hw : ∀ i,φ (w i)=BlumeCapel.weight D H i) :
    (K=0 → (problem basis M w).InFP) ∧ (K≠0 → SharpPHard (problem basis M w)) := by
  constructor
  · intro hK
    subst K
    exact zero_coupling_inFP basis φ M w hM
  · intro hK
    apply nonzero_coupling_hard basis φ K hK M w hM
    intro i
    rw [hw]
    exact BlumeCapel.weight_positive D H i

end PlanarHom.FixedRealBlumeCapel
