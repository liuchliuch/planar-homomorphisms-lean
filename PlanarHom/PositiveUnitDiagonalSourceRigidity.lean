import PlanarHom.OrdinaryFamilyGramSeed
import PlanarHom.PositiveDefiniteDichotomyAssembly
import PlanarHom.PositiveWeightRemovalReduction
import PlanarHom.RectangularNormalizedMomentPrograms

/-! NEW literal unit-diagonal source rigidity. The positive-definite seed is a
compiled two-edge Gram and fixed entrywise power; the original matrix need not
be invertible. Invertibility is a proved conclusion. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity ClosedMatrixFamily TypedBipartiteContext
variable {q bt ut : ℕ} [Nonempty (Fin q)]

theorem homogeneous_unit_diagonal_tensor_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hpos : ∀i j,0<L.matrices 0 i j) (hdiag : ∀i,L.matrices 0 i i=1)
    (hinj : Function.Injective (L.matrices 0)) (hnot : ¬PromisedSharpPHard L.problem) :
    ∃ d : ℕ, ∃ e : Fin q ≃ Boolean.Cube d, ∃ ρ : Fin d → ℝ,
      (∀r,0<ρ r ∧ ρ r≠1) ∧ Matrix.reindex e e (L.matrices 0)=Boolean.tensor ρ ∧
      IsUnit (L.matrices 0) := by
  have hproj := positive_unitDiagonal_rows_nonproportional (L.matrices 0) hpos hs hdiag hinj
  have hseed := L.ordinaryFamily_positive_seed hs hpos hproj
  obtain ⟨W⟩ := L.ordinaryFamily_common_chart hPotts hunit ⟨_,hseed⟩ hnot
  have hherm : (L.matrices 0).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using hs j i
  obtain ⟨ρ,hρ,he,hU⟩ := W.positive_unit_core_of_biased_foundation
    BiasedPositiveHardness.biasedBooleanFoundation L.ordinaryFamily_algebraic
    L.ordinaryFamily_effective L.ordinaryFamily_gadgets L.problem
    (fun N hN=>⟨L.ordinaryFamily_source hunit N hN⟩) hnot _
    (L.ordinaryFamily_generator hherm) hpos hdiag hinj
  exact ⟨W.dimension,W.graphIso.toEquiv,ρ,hρ,he,hU⟩

theorem unit_diagonal_tensor_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q bt ut) (old : Fin bt) (hunit : ∀i,L.weights i=1)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hpos : ∀i j,0<L.matrices old i j) (hdiag : ∀i,L.matrices old i i=1)
    (hinj : Function.Injective (L.matrices old)) (hnot : ¬PromisedSharpPHard L.problem) :
    ∃ d : ℕ, ∃ e : Fin q ≃ Boolean.Cube d, ∃ ρ : Fin d → ℝ,
      (∀r,0<ρ r ∧ ρ r≠1) ∧ Matrix.reindex e e (L.matrices old)=Boolean.tensor ρ ∧
      IsUnit (L.matrices old) := by
  let S := unitLanguage (fun _:Fin 1=>L.matrices old) (fun _=>L.matrices_algebraic old)
  have red := S.relabelReduction L (fun _=>old) (fun u:Fin 0=>u.elim0)
    (fun _ _ _=>rfl) (fun u=>u.elim0) (fun i=>(hunit i).symm)
  exact S.homogeneous_unit_diagonal_tensor_of_not_hard hPotts (fun _=>rfl)
    hs hpos hdiag hinj (fun hh=>hnot (hh.trans red))


/-- Positive background removal is an actual source compiler, applied only
after unit diagonal and distinct rows supply the nonproportionality premise. -/
theorem weighted_unit_diagonal_tensor_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q bt ut) (old : Fin bt)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hpos : ∀i j,0<L.matrices old i j) (hdiag : ∀i,L.matrices old i i=1)
    (hinj : Function.Injective (L.matrices old)) (hw : ∀i,0<L.weights i)
    (hnot : ¬PromisedSharpPHard L.problem) :
    ∃ d : ℕ, ∃ e : Fin q ≃ Boolean.Cube d, ∃ ρ : Fin d → ℝ,
      (∀r,0<ρ r ∧ ρ r≠1) ∧ Matrix.reindex e e (L.matrices old)=Boolean.tensor ρ ∧
      IsUnit (L.matrices old) := by
  have hnz : ∀i,L.matrices old i≠0 := by
    intro i hh
    exact (ne_of_gt (hpos i i)) (congrFun hh i)
  have hproj := positive_unitDiagonal_rows_nonproportional (L.matrices old) hpos hs hdiag hinj
  let S := unitLanguage (fun _:Fin 1=>L.matrices old) (fun _=>L.matrices_algebraic old)
  have present := S.presentationDescentReduction L.field L.basis
    (fun _:Fin 1=>L.matricesK old) (fun u:Fin 0=>u.elim0) (fun _=>1)
    (fun _ _ _=>rfl) (fun u=>u.elim0) (fun _=>rfl)
  have selected := EndpointUnarySource.selectedMatrixReduction L.basis L.matricesK L.unariesK
    (fun _=>1) old
  have remove := PositiveWeightRemoval.removePositiveWeights L.basis L.matricesK L.unariesK
    L.weightsK old hs hw hnz hproj
  have red := present.trans (selected.trans remove)
  exact S.homogeneous_unit_diagonal_tensor_of_not_hard hPotts (fun _=>rfl)
    hs hpos hdiag hinj (fun hh=>hnot (hh.trans red))

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
