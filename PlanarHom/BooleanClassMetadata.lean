import PlanarHom.BooleanClassTowerMoments
import PlanarHom.BooleanSampledMetadataCertificates

/-! NEW exact correspondence between the computed grouped metadata and the
literal spectral choices of the input edge occurrences. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanClassMetadata
open BooleanFieldTower BooleanFieldTowerAlgebra BooleanGroupedMetadataMachines
open BooleanClassTowerMoments BooleanFieldCollision BooleanSpectralCounts
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {b d m : ℕ}

def nodeIndex (cls : Fin d→Fin b) (c a w : Fin b→K) (g0 : Fin b) (q : ℚ)
    (ε : Fin m→Fin d→Bool) : Fin (nodes c a w (multiplicity cls) g0 (m,q)).length :=
  Classical.choose (List.mem_iff_get.mp (node_mem c a w (multiplicity cls) g0 (m,q)
    (count cls ε) (fun i=>count_le_total cls ε i)))

theorem nodeIndex_get (cls : Fin d→Fin b) (c a w : Fin b→K) (g0 : Fin b) (q : ℚ)
    (ε : Fin m→Fin d→Bool) :
    (nodes c a w (multiplicity cls) g0 (m,q)).get (nodeIndex cls c a w g0 q ε) =
      (count cls ε g0,spectral c a w (algebraMap ℚ K q) (total cls m) (count cls ε)) :=
  Classical.choose_spec (List.mem_iff_get.mp (node_mem c a w (multiplicity cls) g0 (m,q)
    (count cls ε) (fun i=>count_le_total cls ε i)))

theorem nodeIndex_value (cls : Fin d→Fin b) (c a w : Fin b→K) (g0 : Fin b) (q : ℚ)
    (ε : Fin m→Fin d→Bool) :
    ofTower (D a w (algebraMap ℚ K q)) b
      ((nodes c a w (multiplicity cls) g0 (m,q)).get (nodeIndex cls c a w g0 q ε)).2 =
      nodeValue cls c a w (algebraMap ℚ K q) ε := by
  rw [nodeIndex_get]
  rfl

theorem target_index_value (cls : Fin d→Fin b) (c a w : Fin b→K) (g0 : Fin b) (q : ℚ)
    (ε : Fin m→Fin d→Bool)
    (h : count cls ε g0 < (targets c a w (multiplicity cls) g0 (m,q)).length) :
    ofTower (D a w (algebraMap ℚ K q)) b
      (targets c a w (multiplicity cls) g0 (m,q))[count cls ε g0] =
      retainedNode cls c a w (algebraMap ℚ K q) g0 ε := by
  rw [targets_getElem]
  rw [target_eq c a w (multiplicity cls) g0 (m,q) _ (count_le_total cls ε g0)]
  rfl

theorem sampled_radicands_ne_zero (f : K→+*ℝ) (c a w : Fin b→K) (mult : Fin b→ℕ)
    (ell m : ℕ) (q : ℚ) (hq:q∈BooleanEffectiveLengthSamples.samples c a w mult ell m)
    (hp:BooleanExceptionalSource.SeparatedParameters
      (fun i=>f (c i)) (fun i=>f (a i)) (fun i=>f (w i))) :
    ∀i:Fin b,D a w (algebraMap ℚ K q) i.val≠0 := by
  have hx:=(BooleanEffectiveLengthSamples.samples_bounds c a w mult ell m q hq).1
  intro i hz
  have ht:=BooleanConjugateProducts.radicand_pos (a:=f (a i)) (hp.w_pos i) hx
  have he : f (D a w (algebraMap ℚ K q) i.val) =
      (f (a i))^2+(f (w i))^2*(q:ℝ)^2 := by
    simp [D,radicands,_root_.map_add,_root_.map_mul,_root_.map_pow]
  rw [hz,_root_.map_zero] at he
  linarith

end PlanarHom.BooleanClassMetadata
