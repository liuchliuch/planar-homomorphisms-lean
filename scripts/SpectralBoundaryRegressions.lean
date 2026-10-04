import PlanarHom.GlobalDomainSpectralAvailability

open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open RealSpectralInterpolation
noncomputable section

-- Zero PSD source has exactly the zero range projector.
example : rangeProjector (0 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  simp [rangeProjector,AlgebraicSpectralData.rangeProjector]

-- A repeated eigenvalue is treated as its whole eigenspace, not a chosen rank-one splitting.
def repeatedEigenvalue : Matrix (Fin 2) (Fin 2) ℝ := algebraMap ℝ _ 2
example : rangeProjector repeatedEigenvalue = 1 := by
  unfold rangeProjector AlgebraicSpectralData.rangeProjector repeatedEigenvalue
  rw [cfc_algebraMap]
  norm_num
example : AlgebraicSpectralData.spectralProjector repeatedEigenvalue 2 = 1 := by
  unfold AlgebraicSpectralData.spectralProjector repeatedEigenvalue
  rw [cfc_algebraMap]
  norm_num
example : AlgebraicSpectralData.spectralProjector repeatedEigenvalue 3 = 0 := by
  unfold AlgebraicSpectralData.spectralProjector repeatedEigenvalue
  rw [cfc_algebraMap]
  norm_num
example : rationalPower repeatedEigenvalue (-1) = algebraMap ℝ _ (1/2 : ℝ) := by
  unfold rationalPower AlgebraicSpectralData.rationalPower repeatedEigenvalue
  rw [cfc_algebraMap]
  norm_num [Real.rpow_neg_one]

-- No marked occurrence keeps the original vertex and unary occurrences.
def unmarkedGraph : MixedCode := ⟨1,[],[(0,0)]⟩
#guard unmarkedGraph.stretchLabelLength 1 0 5 == unmarkedGraph
#guard ExponentProductTables.representatives (fun _ : Fin 2 => (2 : ℚ)) (fun _ => 1) 0 == [(1,1)]

-- Positive occurrence count with an all-zero scalar alphabet submits no bases.
#guard ExponentProductTables.representatives (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 0) 2 == []
#guard ProductInterpolationPreparationMachines.recoverContext (fun _ : Fin 1 => (0 : ℚ))
  (ProductInterpolationPreparationMachines.metadataFor (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 0) 2,[]) == 0

#print axioms RealSpectralInterpolation.rangeProjector_on_image
#print axioms RealSpectralInterpolation.rangeProjector_on_kernel
#print axioms AlgebraicProductInterpolation.RealLanguage.lemma33_range
#print axioms AlgebraicProductInterpolation.RealLanguage.lemma33_rationalPower


-- Global C remains usable between narrower prescribed endpoint domains.
-- Companion label0 retains its original restricted endpoint table.
private def ambientDomains (i : Fin 3) : Set (Fin 2) :=
  if i.val=0 then {0} else if i.val=1 then Set.univ else {1}
private def companionPolicy (_ : Fin 2) (x y : Fin 3) : Prop := x=0 ∧ y=0
private def emptyUnaryPolicy : Fin 0 → Fin 3 → Prop := fun i => Fin.elim0 i
example : PrescribedDomains.withGlobalMatrix companionPolicy 1 1 0 2 := by
  simp [PrescribedDomains.withGlobalMatrix]
example : ¬ PrescribedDomains.withGlobalMatrix companionPolicy 1 0 0 2 := by
  norm_num [PrescribedDomains.withGlobalMatrix,companionPolicy]
  decide
example : PrescribedDomains.PathDomainTyping
    (PrescribedDomains.withGlobalMatrix companionPolicy 1) 1 1 0 2 :=
  PrescribedDomains.withGlobalMatrix_pathTyping _ _ _ _ _

example (L : AlgebraicProductInterpolation.RealLanguage 2 2 0)
    (hunit : ∀ i, L.weights i=1) (hC : (L.matrices 1).PosSemidef) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction
      (L.domainProblem ambientDomains (PrescribedDomains.withGlobalMatrix companionPolicy 1) emptyUnaryPolicy) base) :
    PromisePolyTimeTuringReduction
      (L.domainRangeTargetProblem ambientDomains
        (PrescribedDomains.withGlobalMatrix companionPolicy 1) emptyUnaryPolicy 1 hC) base :=
  L.lemma33_global_domain_range hunit ambientDomains companionPolicy emptyUnaryPolicy 1 1
    (by simp [ambientDomains]) hC base available

#print axioms AlgebraicProductInterpolation.RealLanguage.lemma33_global_domain_range
#print axioms AlgebraicProductInterpolation.RealLanguage.lemma33_global_domain_rationalPower
