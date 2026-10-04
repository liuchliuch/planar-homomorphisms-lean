import PlanarHom.EndpointLoopParameterAvailability
import PlanarHom.BooleanFamilyPosDef
import PlanarHom.ClosedFamilyCoordinateTransport

/-! The computable field-valued loop/distance family is literally equation5.2
in any fixed Boolean chart, with no assumed logarithmic-support premise. -/
noncomputable section
open Classical
namespace PlanarHom.BooleanNormalizedFamilyIdentification
open BooleanPDNormalization CubeTensorExponential MatrixCoordinateTransport
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K] {q d : ℕ}

private theorem factors_posDef (θ w : Fin d→ℝ) (hθ : ∀r,0<θ r)
    (hw : ∀r,0<w r) (hw1 : ∀r,w r<1) : ∀r,(normalForm (θ r) (w r)).PosDef := by
  intro r
  apply BooleanFamilyPosDef.normalForm_posDef _ _ (hθ r)
  nlinarith [hw r,hw1 r]

theorem source_posDef (A : Matrix (Fin q) (Fin q) K) (e : Fin q≃Boolean.Cube d)
    (γ : K) (hγ : 0<(γ : ℝ)) (θ w : Fin d→ℝ)
    (hθ : ∀r,0<θ r) (hw : ∀r,0<w r) (hw1 : ∀r,w r<1)
    (hsource : Matrix.reindex e e (SpectralFieldPresentation.realMatrix A)=
      (γ : ℝ) • tensor (fun r=>normalForm (θ r) (w r))) :
    (SpectralFieldPresentation.realMatrix A).PosDef := by
  apply (ClosedMatrixFamily.reindex_posDef_iff e _).mp
  rw [hsource]
  exact (BooleanLogPositivity.tensor_posDef _ (factors_posDef θ w hθ hw hw1)).smul hγ

theorem reindexed_support (A : Matrix (Fin q) (Fin q) K) (e : Fin q≃Boolean.Cube d)
    (γ : K) (hγ : 0<(γ : ℝ)) (θ w : Fin d→ℝ)
    (hθ : ∀r,0<θ r) (hw : ∀r,0<w r) (hw1 : ∀r,w r<1)
    (hsource : Matrix.reindex e e (SpectralFieldPresentation.realMatrix A)=
      (γ : ℝ) • tensor (fun r=>normalForm (θ r) (w r))) :
    LogarithmicSupport.logSupport (Matrix.reindex e e (SpectralFieldPresentation.realMatrix A))=
      Boolean.cubeGraph d := by
  rw [hsource]
  exact BooleanLogPositivity.matrixLog_smul_tensor_support _ (factors_posDef θ w hθ hw hw1)
    (fun r=>by simpa [normalForm] using hw r) hγ

def sourceGraphIso (A : Matrix (Fin q) (Fin q) K) (e : Fin q≃Boolean.Cube d)
    (γ : K) (hγ : 0<(γ : ℝ)) (θ w : Fin d→ℝ)
    (hθ : ∀r,0<θ r) (hw : ∀r,0<w r) (hw1 : ∀r,w r<1)
    (hsource : Matrix.reindex e e (SpectralFieldPresentation.realMatrix A)=
      (γ : ℝ) • tensor (fun r=>normalForm (θ r) (w r))) :
    DistanceKernelAvailability.graph A ≃g Boolean.cubeGraph d where
  toEquiv:=e
  map_rel_iff' := by
    intro i j
    have h:= (logSupport_reindex_iso e (SpectralFieldPresentation.realMatrix A)
      (source_posDef A e γ hγ θ w hθ hw hw1 hsource)).map_rel_iff (a:=i) (b:=j)
    change (LogarithmicSupport.logSupport (Matrix.reindex e e (SpectralFieldPresentation.realMatrix A))).Adj
      (e i) (e j) ↔ (DistanceKernelAvailability.graph A).Adj i j at h
    rw [reindexed_support A e γ hγ θ w hθ hw hw1 hsource] at h
    exact h

theorem source_positive_log (A : Matrix (Fin q) (Fin q) K) (e : Fin q≃Boolean.Cube d)
    (γ : K) (hγ : 0<(γ : ℝ)) (θ w : Fin d→ℝ)
    (hθ : ∀r,0<θ r) (hw : ∀r,0<w r) (hw1 : ∀r,w r<1)
    (hsource : Matrix.reindex e e (SpectralFieldPresentation.realMatrix A)=
      (γ : ℝ) • tensor (fun r=>normalForm (θ r) (w r))) :
    ∀i j,(DistanceKernelAvailability.graph A).Adj i j→
      0<EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix A) i j := by
  intro i j hij
  have hadj:=(sourceGraphIso A e γ hγ θ w hθ hw hw1 hsource).map_rel_iff.mpr hij
  have hp:=BooleanLogPositivity.matrixLog_smul_tensor_edge_pos _ (factors_posDef θ w hθ hw hw1)
    (fun r=>by simpa [normalForm] using hw r) hγ (e i) (e j) hadj
  rw [←hsource,matrixLog_reindex e (source_posDef A e γ hγ θ w hθ hw hw1 hsource)] at hp
  simpa [Matrix.reindex_apply,Matrix.submatrix_apply] using hp

/-- Literal equation5.2 for the actually computed field-valued family. -/
theorem family_real (A : Matrix (Fin q) (Fin q) K) (e : Fin q≃Boolean.Cube d)
    (γ : K) (hγ : 0<(γ : ℝ)) (θ w : Fin d→ℝ)
    (hθ : ∀r,0<θ r) (hw : ∀r,0<w r) (hw1 : ∀r,w r<1)
    (hsource : Matrix.reindex e e (SpectralFieldPresentation.realMatrix A)=
      (γ : ℝ) • tensor (fun r=>normalForm (θ r) (w r))) (k : ℕ) (x : ℚ) :
    Matrix.reindex e e (SpectralFieldPresentation.realMatrix
      (EndpointLoopParameterAvailability.family A k ((γ^(2*k+1))⁻¹) x))=
      tensor (fun r=>normalForm ((θ r)^(2*k+1)) (w r*(x : ℝ))) := by
  have hk:=reindex_distanceKernel (sourceGraphIso A e γ hγ θ w hθ hw hw1 hsource) (x : ℝ)
  change Matrix.reindex e e (EntropyCompletion.distanceKernel (DistanceKernelAvailability.graph A) (x : ℝ))=
    EntropyCompletion.distanceKernel (Boolean.cubeGraph d) (x : ℝ) at hk
  have hc : (((γ^(2*k+1))⁻¹ : K) : ℝ)=((γ : ℝ)^(2*k+1))⁻¹ := by
    change K.val.toRingHom ((γ^(2*k+1))⁻¹)=((γ : ℝ)^(2*k+1))⁻¹
    rw [map_inv₀,map_pow]
    rfl
  calc
    _ = (fun z z'=>(((γ : ℝ)^(2*k+1))⁻¹ • EndpointLoopMachines.decorated
        (Matrix.reindex e e (SpectralFieldPresentation.realMatrix A)) k) z z' *
      (Matrix.reindex e e (EntropyCompletion.distanceKernel (DistanceKernelAvailability.graph A) (x : ℝ))) z z') := by
      ext z z'
      simp [EndpointLoopParameterAvailability.family,EndpointLoopMachines.decorated,
        SpectralFieldPresentation.realMatrix,Matrix.reindex_apply,Matrix.submatrix_apply,
        Matrix.smul_apply,smul_eq_mul,DistanceKernelEvaluationMachines.matrix,
        EntropyCompletion.distanceKernel,mul_assoc,hc]
    _ = _ := by
      rw [hsource,hk]
      exact BooleanLoopNormalization.source_family (γ : ℝ) (ne_of_gt hγ) θ w
        (fun r=>ne_of_gt (hθ r)) k (x : ℝ)

end PlanarHom.BooleanNormalizedFamilyIdentification
