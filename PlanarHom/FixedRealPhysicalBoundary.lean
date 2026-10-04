import PlanarHom.FixedRealPositiveWeightedClassification
import PlanarHom.PhysicalModelBoundaryValues

/-! The source problem and zero-interaction boundary used by the exact real
physical applications. The output always stays in the given presentation. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealPhysicalModels
open DensePolynomial RepresentedBit
variable {d e : ℕ} {K C : Type} [Field K] [Algebra (RationalFunction d) K] [Fintype C]

abbrev problem (basis : Module.Basis (Fin e) (RationalFunction d) K)
    (M : Matrix C C K) (w : C → K) : Problem :=
  FixedRealComponents.problem basis (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) w

 theorem all_ones_inFP (basis : Module.Basis (Fin e) (RationalFunction d) K)
    (w : C → K) : (problem basis (fun _ _ => 1) w).InFP := by
  let f : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  have h := FixedRealGraphEvaluation.color basis f (fun _ _ : Fin (Fintype.card C) => (1 : K)*1)
    (fun i => w (f.symm i)) (FixedRealGraphEvaluation.rankOne basis (fun _ => 1) (fun i => w (f.symm i)))
  have h' : FixedRealGraphEvaluation.Evaluable basis (fun _ _ : C => (1 : K)) w := by
    simpa only [one_mul,f.symm_apply_apply] using h
  exact FixedRealGraphEvaluation.inFP basis _ _ h'

 theorem mapped_all_ones_inFP (basis : Module.Basis (Fin e) (RationalFunction d) K)
    (φ : K →+* ℝ) (M : Matrix C C K) (w : C → K)
    (hM : ∀ i j,φ (M i j)=1) : (problem basis M w).InFP := by
  have he : M=(fun _ _ => 1) := by
    funext i j
    exact φ.injective (by simpa only [map_one] using hM i j)
  rw [he]
  exact all_ones_inFP basis w

end PlanarHom.FixedRealPhysicalModels
