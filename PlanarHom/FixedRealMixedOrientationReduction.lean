import PlanarHom.FixedRealMixedOrientationConnected

/-! Full A.2 prescribed bipartite orientation with every finite mixed companion
retained. Input component extraction preserves arbitrary ordinary unaries and
one reserved side tag per vertex. Only the proved common crossing condition
allows replacement by one root-side restriction on each component. -/
noncomputable section
open Classical
namespace PlanarHom.MixedOrientation
open Complexity Complexity.MixedCode PrescribedDomains

def sidePolicies (b:ℕ) : Fin b→Fin 2→Fin 2→Prop := fun _ i j=>i≠j
def unaryPolicies (u:ℕ) : Fin u→Fin 2→Prop := fun _ _=>True

theorem encoded_tagged {b u:ℕ} (code:MixedCode)
    (h:EncodedGraph (sidePolicies b) (unaryPolicies u) code) : Tagged b u code := by
  have hp:=h.planarValid
  obtain ⟨g,hg,δ,ht,hplanar,hd⟩:=h
  rw [MixedCode.encoding.decode_encode] at hd
  have he:=Option.some.inj hd
  subst code
  refine ⟨hp,δ,tags_withDomains g hg δ,?_⟩
  intro a ha
  exact ht.1 a ha

end PlanarHom.MixedOrientation
namespace PlanarHom.FixedRealMixedOrientation
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open PrescribedDomains FixedRealRootRestrictions MixedOrientation
variable {n e b u:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def problem (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) (side:C→Bool) : Problem :=
  (presentation basis).problem MixedCode.encoding (EncodedGraph (sidePolicies b) (unaryPolicies u))
    (totalEvaluation M (extendedUnaries U (Bipartite.domains side)) w)

def componentReduction (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) (side:C→Bool) :
    Reduction (taggedProblem basis M U w side) (connectedProblem basis M U w side) := by
  let prep:MixedCode→ℕ×List MixedCode:=fun g=>(0,GraphComponentCode.components g)
  let recov:ℕ×List (Code n e)→Code n e:=fun p=>FixedRealListProduct.product basis p.2
  have hp:FP MixedCode.encoding (BitEncoding.nat.prod MixedCode.encoding.list) prep:=
    (fp_const _ _ 0).pair GraphComponentMachines.fp_components
  have hr:FP (BitEncoding.nat.prod (encoding n e).list) (encoding n e) recov:=
    (PairProjectionMachines.fp_snd _ _).comp (FixedRealListProduct.fp_product basis)
  apply presentationPipeline (presentation basis) (presentation basis) MixedCode.encoding BitEncoding.nat
    MixedCode.encoding MixedCode.normalizer BitEncoding.natNormalizer (Tagged b u)
    (ConnectedTagged b u) _ _ prep recov hp hr
  · exact components_tagged
  · intro g hg bs hbs
    have hb:=FixedRealComponents.represented_answers basis _ bs _ hbs
    obtain ⟨hg,δ,ht,hp⟩:=hg
    refine ⟨FixedRealListProduct.product_valid basis bs hb.1,?_⟩
    change value basis (FixedRealListProduct.product basis bs)=_
    rw [FixedRealListProduct.product_value basis bs hb.1,hb.2,
      totalEvaluation_valid _ _ _ g hg.1]
    exact (GraphComponentCode.evaluate_components g hg.1 _ _ _).symm

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- The retained-label crossing premise is explicit for every binary type.
Original unary factors are arbitrary, and every root background appears once. -/
def corollaryA2_mixed_orientation (M:Fin b→Matrix C C K) (hs:∀l i j,M l i j=M l j i)
    (U:Fin u→C→K) (w:C→K) (hw:∀i,0 < w i) (side:C→Bool)
    (hcross:∀l i j,M l i j≠0→side i≠side j) :
    Reduction (problem basis M U w side) (FixedRealComponents.problem basis M U w) := by
  have enter:Reduction (problem basis M U w side) (taggedProblem basis M U w side):=
    queryReduction (presentation basis) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
      (EncodedGraph (sidePolicies b) (unaryPolicies u)) (Tagged b u)
      (totalEvaluation M (extendedUnaries U (Bipartite.domains side)) w)
      (totalEvaluation M (extendedUnaries U (Bipartite.domains side)) w)
      id (fp_id _) encoded_tagged (fun _ _=>rfl)
  exact (enter.trans (componentReduction basis M U w side)).trans
    (connectedReduction basis M hs U w hw side hcross)

end PlanarHom.FixedRealMixedOrientation
