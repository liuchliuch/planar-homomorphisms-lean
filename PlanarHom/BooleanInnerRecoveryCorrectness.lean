import PlanarHom.BooleanClassMetadata
import PlanarHom.BooleanInnerRecoveryProgram

/-! NEW correctness of the actual inner recovery program on literal mixed
partition-function power answers. All inverse and node promises are derived
from the computed samples and actual occurrence-level spectral expansion. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanInnerRecoveryCorrectness
open Complexity Complexity.MixedCode BooleanTensorSpectral BooleanTensorPartitionMoments
open BooleanFieldTower BooleanFieldTowerAlgebra BooleanGroupedMetadataMachines
open BooleanClassTowerMoments BooleanClassMetadata BooleanSpectralCounts
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {b d bt ut : ℕ}

def sourceMatrix (cls : Fin d→Fin b) (c a w : Fin b→K) (q : ℚ) :
    Matrix (Fin d→Bool) (Fin d→Bool) K :=
  tensor (fun i=>block (c (cls i)) (a (cls i)) (w (cls i)*algebraMap ℚ K q))

def retainedMatrix (cls : Fin d→Fin b) (c a w : Fin b→K) (q : ℚ) (g0 : Fin b) :
    Matrix (Fin d→Bool) (Fin d→Bool) K :=
  tensor (fun i=>if cls i=g0 then block (c (cls i)) (a (cls i))
    (w (cls i)*algebraMap ℚ K q) else 1)

def positiveMoments (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (ω : (Fin d→Bool)→K) (cls : Fin d→Fin b) (c a w : Fin b→K) (q : ℚ) : List K :=
  List.ofFn (fun h : Fin (BooleanInnerRecoveryProgram.queryCount (multiplicity cls)
    (g.markedCount selected.val))=>
    g.evaluate hg (replace M selected ((sourceMatrix cls c a w q)^(h.val+1))) U ω)

/-- The returned value is the actual retained tensor evaluation, including all
unchanged signed companion matrices, ordinary unary occurrences and weights. -/
theorem recover_eq_retained (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (ω : (Fin d→Bool)→K) (cls : Fin d→Fin b) (c a w : Fin b→K) (f : K→+*ℝ)
    (hp:BooleanExceptionalSource.SeparatedParameters
      (fun i=>f (c i)) (fun i=>f (a i)) (fun i=>f (w i)))
    (g0 : Fin b) (hg0:a g0≠0) (ell : ℕ) (q : ℚ)
    (hq:q∈BooleanEffectiveLengthSamples.samples c a w (multiplicity cls) ell
      (g.markedCount selected.val)) :
    BooleanInnerRecoveryProgram.recover c a w (multiplicity cls) g0
      ((g.markedCount selected.val,q),positiveMoments g hg selected M U ω cls c a w q) =
    g.evaluate hg (replace M selected (retainedMatrix cls c a w q g0)) U ω := by
  let m:=g.markedCount selected.val
  let x:=algebraMap ℚ K q
  let ds:=radicandList a w (m,q)
  let ns:=nodes c a w (multiplicity cls) g0 (m,q)
  let ts:=targets c a w (multiplicity cls) g0 (m,q)
  let ys:=positiveMoments g hg selected M U ω cls c a w q
  let Z:=(Fin g.vertices→Fin d→Bool) × (Fin m→Fin d→Bool)
  let index : Z→Fin ns.length:=fun z=>nodeIndex cls c a w g0 q z.2
  let weight : Z→Carrier (BooleanFieldTowerConvolutionMachines.radicands ds) b:=
    coefficient g hg selected M U ω cls a w x
  have hD0:=sampled_radicands_ne_zero f c a w (multiplicity cls) ell m q hq hp
  have hd : BooleanFieldTowerConvolutionMachines.radicands ds = D a w x :=
    BooleanSampledMetadataCertificates.metadata_radicands a w (m,q)
  have hnval (z:Z) : ofTower (D a w x) b (ns[(index z).val].2) = nodeValue cls c a w x z.2 := by
    change ofTower (D a w x) b ((nodes c a w (multiplicity cls) g0 (m,q)).get
      (nodeIndex cls c a w g0 q z.2)).2 = _
    exact nodeIndex_value cls c a w g0 q z.2
  have hlabel (z:Z) : (ns[(index z).val]).1 = count cls z.2 g0 := by
    exact congrArg Prod.fst (nodeIndex_get cls c a w g0 q z.2)
  have hlen : ys.length=BooleanGroupedTableRecoveryMachines.degreeCap ns.length := by
    simp only [ys,positiveMoments,List.length_ofFn]
    exact BooleanInnerRecoveryProgram.queryCount_matches_metadata c a w (multiplicity cls) g0 m q
  have hmom : ∀h:Fin (BooleanGroupedTableRecoveryMachines.degreeCap ns.length),
      algebraMap K (Carrier (BooleanFieldTowerConvolutionMachines.radicands ds) b)
        (ys[h.val]'(by rw [hlen];exact h.isLt)) =
      ∑z:Z,weight z * (ofTower (BooleanFieldTowerConvolutionMachines.radicands ds) b
        (ns[(index z).val].2))^(h.val+1) := by
    intro h
    rw [hd]
    simp_rw [hnval]
    simp only [ys,positiveMoments,List.getElem_ofFn]
    exact BooleanClassTowerMoments.evaluate_power g hg selected M U ω cls c a w x hD0 (h.val+1)
  let value:=g.evaluate hg (replace M selected (retainedMatrix cls c a w q g0)) U ω
  have hval : (∑z:Z,weight z * ofTower (BooleanFieldTowerConvolutionMachines.radicands ds) b
      (ts[(ns[(index z).val]).1]'(node_label_lt_targets c a w (multiplicity cls) g0
        (m,q) _ (List.getElem_mem _)))) = embed b value := by
    rw [hd]
    have ht (z:Z) : ofTower (D a w x) b
        (ts[(ns[(index z).val]).1]'(node_label_lt_targets c a w (multiplicity cls) g0
          (m,q) _ (List.getElem_mem _))) = retainedNode cls c a w x g0 z.2 := by
      simp only [hlabel]
      exact target_index_value cls c a w g0 q z.2 _
    simp_rw [ht]
    exact (BooleanClassTowerMoments.evaluate_retained g hg selected M U ω cls c a w x hD0 g0).symm
  exact BooleanGroupedTableCorrectness.recover_eq_of_weighted_targets_embed b ds ns ts
    (node_label_lt_targets c a w (multiplicity cls) g0 (m,q))
    (BooleanSampledMetadataCertificates.nodes_norm_nonzero f c a w (multiplicity cls) g0 ell m q hq hp)
    (BooleanSampledMetadataCertificates.cross_norm_nonzero c a w (multiplicity cls) g0 ell m q hq hg0)
    index weight ys hlen hmom value hval

end PlanarHom.BooleanInnerRecoveryCorrectness
