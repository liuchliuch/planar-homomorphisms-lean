import PlanarHom.BooleanGroupedMetadataMachines
import PlanarHom.BooleanGroupedTableCorrectness
import PlanarHom.BooleanSampleNormCertificates

/-! The literal FP metadata and sampler discharge all grouped interpolation
inverse promises. No assumed radical-field arithmetic or collision oracle is
added at the point where the actual recovery program is applied. -/
noncomputable section
open Classical
namespace PlanarHom.BooleanSampledMetadataCertificates
open BooleanFieldTower BooleanGroupedMetadataMachines BooleanEffectiveLengthSamples
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {b:ℕ}

theorem metadata_radicands (a w:Fin b→K) (p:Input) :
    BooleanFieldTowerConvolutionMachines.radicands (radicandList a w p)=
      BooleanFieldCollision.radicands a w (algebraMap ℚ K p.2) := by
  funext i
  exact radicandList_getD a w p i

theorem nodes_norm_nonzero (f:K→+*ℝ) (c a w:Fin b→K) (d:Fin b→ℕ) (g0:Fin b)
    (ell m:ℕ) (q:ℚ) (hq:q∈samples c a w d ell m)
    (hp:BooleanExceptionalSource.SeparatedParameters
      (fun i=>f (c i)) (fun i=>f (a i)) (fun i=>f (w i))) :
    ∀z∈nodes c a w d g0 (m,q),
      norm (BooleanFieldTowerConvolutionMachines.radicands (radicandList a w (m,q))) b z.2≠0 := by
  intro z hz
  obtain ⟨k,hk,rfl⟩:=(mem_nodes_iff c a w d g0 (m,q) z).mp hz
  rw [metadata_radicands]
  exact BooleanSampleNormCertificates.sampled_node_norm_ne_zero f c a w d ell m q hq k hp

theorem cross_norm_nonzero (c a w:Fin b→K) (d:Fin b→ℕ) (g0:Fin b)
    (ell m:ℕ) (q:ℚ) (hq:q∈samples c a w d ell m) (hg:a g0≠0) :
    ∀z∈nodes c a w d g0 (m,q),∀v∈nodes c a w d g0 (m,q),z.1≠v.1→
      norm (BooleanFieldTowerConvolutionMachines.radicands (radicandList a w (m,q))) b
        (sub b z.2 v.2)≠0 := by
  intro z hz v hv hne
  obtain ⟨k,hk,rfl⟩:=(mem_nodes_iff c a w d g0 (m,q) z).mp hz
  obtain ⟨l,hl,rfl⟩:=(mem_nodes_iff c a w d g0 (m,q) v).mp hv
  rw [metadata_radicands]
  exact BooleanSampleNormCertificates.sampled_difference_norm_ne_zero c a w d ell m q hq k l
    hk hl ⟨g0,hg,hne⟩

theorem rows_valid (f:K→+*ℝ) (c a w:Fin b→K) (d:Fin b→ℕ) (g0:Fin b)
    (ell m:ℕ) (q:ℚ) (hq:q∈samples c a w d ell m) (hg:a g0≠0)
    (hp:BooleanExceptionalSource.SeparatedParameters
      (fun i=>f (c i)) (fun i=>f (a i)) (fun i=>f (w i))) :
    ∀row∈BooleanGroupedTableRecoveryMachines.rows b
      (nodes c a w d g0 (m,q),targets c a w d g0 (m,q)),
      BooleanGroupedGridRecoverySemantics.RowValid b (radicandList a w (m,q)) row := by
  exact BooleanGroupedTableCorrectness.rows_valid b _ _ _
    (nodes_norm_nonzero f c a w d g0 ell m q hq hp)
    (cross_norm_nonzero c a w d g0 ell m q hq hg)

end PlanarHom.BooleanSampledMetadataCertificates
