import PlanarHom.FixedRealOrientationConnected
import PlanarHom.HomogeneousSourceOrientationComponents

/-! Complete represented-field prescribed homogeneous bipartite orientation
for ordinary disconnected planar inputs. Every intrinsic tag is retained and
canonicalized after actual component extraction; no simultaneous pinning is
assumed. Empty inputs use the proven arbitrary-representative empty product. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealOrientation
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open PrescribedDomains HomogeneousSourceOrientation RootedRestriction FixedRealRootRestrictions
variable {n e:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def problem (M:Matrix C C K) (w:C→K) (side:C→Bool) : Problem :=
  (presentation basis).problem MixedCode.encoding (EncodedGraph sidePolicies emptyPolicies)
    (totalEvaluation (fun _:Fin 1=>M) (extendedUnaries (fun l:Fin 0=>l.elim0) (Bipartite.domains side)) w)

def componentReduction (M:Matrix C C K) (w:C→K) (side:C→Bool) :
    Reduction (problem basis M w side) (connectedProblem basis M w side) := by
  let prep:MixedCode→ℕ×List MixedCode:=fun g=>(0,(GraphComponentCode.components g).map canonicalDomains)
  let recov:ℕ×List (Code n e)→Code n e:=fun p=>FixedRealListProduct.product basis p.2
  have hp:FP MixedCode.encoding (BitEncoding.nat.prod MixedCode.encoding.list) prep:=
    (fp_const _ _ 0).pair (GraphComponentMachines.fp_components.comp
      (ListMapMachines.fp_map _ _ canonicalDomains fp_canonicalDomains))
  have hr:FP (BitEncoding.nat.prod (encoding n e).list) (encoding n e) recov:=
    (PairProjectionMachines.fp_snd _ _).comp (FixedRealListProduct.fp_product basis)
  apply presentationPipeline (presentation basis) (presentation basis) MixedCode.encoding BitEncoding.nat
    MixedCode.encoding MixedCode.normalizer BitEncoding.natNormalizer (EncodedGraph sidePolicies emptyPolicies)
    connectedTypedGraph _ _ prep recov hp hr
  · intro g hg query hquery
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hquery
    exact canonical_components_promises g hg c hc
  · intro g hg bs hbs
    have hb:=FixedRealComponents.represented_answers basis _ bs _ hbs
    refine ⟨FixedRealListProduct.product_valid basis bs hb.1,?_⟩
    change value basis (FixedRealListProduct.product basis bs)=_
    rw [FixedRealListProduct.product_value basis bs hb.1,hb.2,
      totalEvaluation_valid _ _ _ g hg.planarValid.1]
    simpa only [prep,List.map_map,Function.comp_apply] using canonical_components_evaluate g hg
      (fun _:Fin 1=>M) (extendedUnaries (fun l:Fin 0=>l.elim0) (Bipartite.domains side)) w

variable [LinearOrder K] [IsStrictOrderedRing K]

def reduction (M:Matrix C C K) (w:C→K) (hw:∀i,0 < w i) (side:C→Bool)
    (hcross:∀i j,M i j≠0→side i≠side j) :
    Reduction (problem basis M w side)
      (RepresentedRootRestriction.sourceProblem (presentation basis) M w) :=
  (componentReduction basis M w side).trans (connectedReduction basis M w hw side hcross)

end PlanarHom.FixedRealOrientation
