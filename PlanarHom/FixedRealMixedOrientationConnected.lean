import PlanarHom.MixedOrientationSemantics
import PlanarHom.MixedOrientationMachines
import PlanarHom.FixedRealOrientationConnected

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealMixedOrientation
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open PrescribedDomains FixedRealRootRestrictions MixedOrientation
variable {n e b u:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def taggedProblem (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) (side:C→Bool) : Problem :=
  (presentation basis).problem MixedCode.encoding (Tagged b u)
    (totalEvaluation M (extendedUnaries U (Bipartite.domains side)) w)

def connectedProblem (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) (side:C→Bool) : Problem :=
  (presentation basis).problem MixedCode.encoding (ConnectedTagged b u)
    (totalEvaluation M (extendedUnaries U (Bipartite.domains side)) w)

variable [LinearOrder K] [IsStrictOrderedRing K]

def connectedReduction (M:Fin b→Matrix C C K) (hs:∀l i j,M l i j=M l j i)
    (U:Fin u→C→K) (w:C→K) (hw:∀i,0 < w i) (side:C→Bool)
    (hcross:∀l i j,M l i j≠0→side i≠side j) :
    Reduction (connectedProblem basis M U w side) (FixedRealComponents.problem basis M U w) := by
  let data₀:=MixedRootedRestriction.exists_computed_queries M U w hw (Bipartite.domains side 0)
  let s₀:=Classical.choose data₀
  let graphs₀:=Classical.choose (Classical.choose_spec data₀)
  let c₀:=Classical.choose (Classical.choose_spec (Classical.choose_spec data₀))
  have h₀:=Classical.choose_spec (Classical.choose_spec (Classical.choose_spec data₀))
  let data₁:=MixedRootedRestriction.exists_computed_queries M U w hw (Bipartite.domains side 1)
  let s₁:=Classical.choose data₁
  let graphs₁:=Classical.choose (Classical.choose_spec data₁)
  let c₁:=Classical.choose (Classical.choose_spec (Classical.choose_spec data₁))
  have h₁:=Classical.choose_spec (Classical.choose_spec (Classical.choose_spec data₁))
  let P:=presentation basis
  let ops:=FixedRealRootRestriction.arithmetic basis
  apply presentationPipeline P P MixedCode.encoding BitEncoding.bool MixedCode.encoding MixedCode.normalizer
    BitEncoding.boolNormalizer (ConnectedTagged b u) (PlanarValid b u)
    (totalEvaluation M (extendedUnaries U (Bipartite.domains side)) w) (totalEvaluation M U w)
    (prepareSides graphs₀ graphs₁) (FixedRealOrientation.recoverSides basis c₀ c₁)
    (fp_prepareSides graphs₀ graphs₁) (FixedRealOrientation.fp_recoverSides basis c₀ c₁)
  · intro code hc query hquery
    obtain ⟨⟨hp,δ,ht,hproper⟩,hconn,hn⟩:=hc
    have hp':(strip u code).PlanarValid b u:=⟨strip_valid code hp.1,hp.2⟩
    simp only [prepareSides] at hquery
    split at hquery
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hquery
      exact MixedRootedCodeMachines.attach_planarValid _ (graphs₁ j).2.2.2.property _ hp' ⟨0,hn⟩
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hquery
      exact MixedRootedCodeMachines.attach_planarValid _ (graphs₀ j).2.2.2.property _ hp' ⟨0,hn⟩
  · intro code hc bs hbs
    have hb:=FixedRealComponents.represented_answers basis _ bs (totalEvaluation M U w) hbs
    obtain ⟨⟨hp,δ,ht,hproper⟩,hconn,hn⟩:=hc
    have hp':(strip u code).PlanarValid b u:=⟨strip_valid code hp.1,hp.2⟩
    have htag:=rootSide_tags code δ ht hn
    change P.valid (FixedRealOrientation.recoverSides basis c₀ c₁ ((prepareSides graphs₀ graphs₁ code).1,bs)) ∧
      P.value (FixedRealOrientation.recoverSides basis c₀ c₁ ((prepareSides graphs₀ graphs₁ code).1,bs))=totalEvaluation _ _ _ code
    rw [totalEvaluation_valid _ _ _ _ hp.1,tagged_eq_root code hp.1 δ ht hproper hconn ⟨0,hn⟩ M hs U w side hcross]
    by_cases hd₁:δ ⟨0,hn⟩=1
    · simp only [prepareSides,htag,hd₁,decide_true,↓reduceIte,FixedRealOrientation.recoverSides] at hb ⊢
      have hy:bs.map P.value=List.ofFn (fun j=>totalEvaluation M U w
          (MixedRootedCodeMachines.attach (graphs₁ j).2.2.2.val (0,strip u code))) := by
        simpa only [FixedRealMixedRootRestriction.prepare,List.map_ofFn] using hb.2
      have hr:=ops.dot_list s₁ c₁ bs hb.1 _ hy
      exact ⟨hr.1,hr.2.trans (h₁ (strip u code) hp' ⟨0,hn⟩).symm⟩
    · have hd₀:δ ⟨0,hn⟩=0:=by
        apply Fin.ext
        have hl:=(δ ⟨0,hn⟩).isLt
        have hne:(δ ⟨0,hn⟩).val≠1:=fun h=>hd₁ (Fin.ext h)
        change (δ ⟨0,hn⟩).val=0
        omega
      simp only [prepareSides,htag,hd₀,show (0:Fin 2)≠1 by decide,decide_false,Bool.false_eq_true,↓reduceIte,
        FixedRealOrientation.recoverSides] at hb ⊢
      have hy:bs.map P.value=List.ofFn (fun j=>totalEvaluation M U w
          (MixedRootedCodeMachines.attach (graphs₀ j).2.2.2.val (0,strip u code))) := by
        simpa only [FixedRealMixedRootRestriction.prepare,List.map_ofFn] using hb.2
      have hr:=ops.dot_list s₀ c₀ bs hb.1 _ hy
      exact ⟨hr.1,hr.2.trans (h₀ (strip u code) hp' ⟨0,hn⟩).symm⟩

end PlanarHom.FixedRealMixedOrientation
