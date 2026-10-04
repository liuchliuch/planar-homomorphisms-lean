import PlanarHom.FixedRealSupportRestriction
import PlanarHom.RepresentedFixedLinearListSemantics
import PlanarHom.HomogeneousSourceOrientationCrossing

/-! Represented-field prescribed bipartite orientation on connected inputs.
Only one root-side restriction is applied, with the original positive weight
included once, and the literal fixed rooted attachment batch is queried. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealOrientation
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open PrescribedDomains HomogeneousSourceOrientation RootedRestriction FixedRealRootRestrictions
variable {n e:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def connectedProblem (M:Matrix C C K) (w:C→K) (side:C→Bool) : Problem :=
  (presentation basis).problem MixedCode.encoding connectedTypedGraph
    (totalEvaluation (fun _:Fin 1=>M) (extendedUnaries (fun l:Fin 0=>l.elim0) (Bipartite.domains side)) w)

def recoverSides {k₀ k₁:ℕ} (c₀:Fin k₀→K) (c₁:Fin k₁→K) (p:Bool×List (Code n e)) : Code n e :=
  if p.1 then (FixedRealRootRestriction.arithmetic basis).dot k₁ (fun i=>(presentation basis).constant (c₁ i)) p.2
  else (FixedRealRootRestriction.arithmetic basis).dot k₀ (fun i=>(presentation basis).constant (c₀ i)) p.2

theorem fp_recoverSides {k₀ k₁:ℕ} (c₀:Fin k₀→K) (c₁:Fin k₁→K) :
    FP (BitEncoding.bool.prod (encoding n e).list) (encoding n e) (recoverSides basis c₀ c₁) := by
  have h:=PairProjectionMachines.fp_snd BitEncoding.bool (encoding n e).list
  have hp:FP (BitEncoding.bool.prod (encoding n e).list) BitEncoding.bool (fun p=>decide (p.1=true)):=
    (PairProjectionMachines.fp_fst _ _).congr (fun _=>by simp)
  exact hp.ite (h.comp ((FixedRealRootRestriction.arithmetic basis).fp_dot _ _))
    (h.comp ((FixedRealRootRestriction.arithmetic basis).fp_dot _ _))

variable [LinearOrder K] [IsStrictOrderedRing K]

def connectedReduction (M:Matrix C C K) (w:C→K) (hw:∀i,0 < w i) (side:C→Bool)
    (hcross:∀i j,M i j≠0→side i≠side j) :
    Reduction (connectedProblem basis M w side)
      (RepresentedRootRestriction.sourceProblem (presentation basis) M w) := by
  let data₀:=exists_computed_root_queries M w hw (Bipartite.domains side 0)
  let k₀:=Classical.choose data₀
  let graphs₀:=Classical.choose (Classical.choose_spec data₀)
  let c₀:=Classical.choose (Classical.choose_spec (Classical.choose_spec data₀))
  have h₀:=Classical.choose_spec (Classical.choose_spec (Classical.choose_spec data₀))
  let data₁:=exists_computed_root_queries M w hw (Bipartite.domains side 1)
  let k₁:=Classical.choose data₁
  let graphs₁:=Classical.choose (Classical.choose_spec data₁)
  let c₁:=Classical.choose (Classical.choose_spec (Classical.choose_spec data₁))
  have h₁:=Classical.choose_spec (Classical.choose_spec (Classical.choose_spec data₁))
  let P:=presentation basis
  let ops:=FixedRealRootRestriction.arithmetic basis
  let M₀:=fun _:Fin 1=>M
  let U₀:Fin 0→C→K:=fun l=>l.elim0
  apply presentationPipeline P P MixedCode.encoding BitEncoding.bool MixedCode.encoding MixedCode.normalizer
    BitEncoding.boolNormalizer connectedTypedGraph (PlanarValid 1 0)
    (totalEvaluation M₀ (extendedUnaries U₀ (Bipartite.domains side)) w) (totalEvaluation M₀ U₀ w)
    (prepareSides graphs₀ graphs₁) (recoverSides basis c₀ c₁) (fp_prepareSides graphs₀ graphs₁)
    (fp_recoverSides basis c₀ c₁)
  · intro code hc query hquery
    obtain ⟨he,hconn,hn⟩:=hc
    obtain ⟨g,hg,δ,ht,hp,hd⟩:=he
    rw [MixedCode.encoding.decode_encode] at hd
    have heq:=Option.some.inj hd
    subst code
    have hn':0 < g.vertices:=hn
    simp only [prepareSides,eraseDomains_withDomains g hg δ] at hquery
    split at hquery
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hquery
      exact RootedCodeMachines.attach_planarValid _ (graphs₁ j).2.2.property 0 _ ⟨hg,hp⟩ ⟨0,hn'⟩ (by decide)
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hquery
      exact RootedCodeMachines.attach_planarValid _ (graphs₀ j).2.2.property 0 _ ⟨hg,hp⟩ ⟨0,hn'⟩ (by decide)
  · intro code hc bs hbs
    have hb:=FixedRealComponents.represented_answers basis _ bs (totalEvaluation M₀ U₀ w) hbs
    obtain ⟨he,hconn,hn⟩:=hc
    obtain ⟨g,hg,δ,ht,hp,hd⟩:=he
    rw [MixedCode.encoding.decode_encode] at hd
    have heq:=Option.some.inj hd
    subst code
    have hn':0 < g.vertices:=hn
    have hconn':(GraphComponentCode.support g).Connected:=hconn
    have htag:=rootSide_withDomains g hg δ hn'
    change P.valid (recoverSides basis c₀ c₁ ((prepareSides graphs₀ graphs₁ _).1,bs)) ∧
      P.value (recoverSides basis c₀ c₁ ((prepareSides graphs₀ graphs₁ _).1,bs))=totalEvaluation M₀ _ w _
    rw [totalEvaluation_valid _ _ _ _ (withDomains_valid g hg δ),
      evaluate_withDomains_eq_rootRestricted_of_crosses g hg hconn' ⟨0,hn'⟩ M w side hcross δ
        (typed_proper g hg δ ht)]
    by_cases hd₁:δ ⟨0,hn'⟩=1
    · simp only [prepareSides,htag,hd₁,decide_true,Bool.true_eq,↓reduceIte,recoverSides] at hb ⊢
      have hy:bs.map P.value=List.ofFn (fun j=>totalEvaluation M₀ U₀ w
          (RootedCodeMachines.attach (graphs₁ j).2.2.val 0 (0,g))) := by
        simpa only [eraseDomains_withDomains g hg δ,RootedRestriction.prepare,List.map_ofFn] using hb.2
      have hr:=ops.dot_list k₁ c₁ bs hb.1 _ hy
      refine ⟨hr.1,hr.2.trans ?_⟩
      simpa only [MultiGraph.atRoot_restricted,hd₁] using (h₁ g ⟨hg,hp⟩ ⟨0,hn'⟩).symm
    · have hd₀:δ ⟨0,hn'⟩=0:=by
        apply Fin.ext
        have hl:=(δ ⟨0,hn'⟩).isLt
        have hn:(δ ⟨0,hn'⟩).val≠1:=fun h=>hd₁ (Fin.ext h)
        change (δ ⟨0,hn'⟩).val=0
        omega
      simp only [prepareSides,htag,hd₀,show (0:Fin 2)≠1 by decide,decide_false,Bool.false_eq_true,↓reduceIte,recoverSides] at hb ⊢
      have hy:bs.map P.value=List.ofFn (fun j=>totalEvaluation M₀ U₀ w
          (RootedCodeMachines.attach (graphs₀ j).2.2.val 0 (0,g))) := by
        simpa only [eraseDomains_withDomains g hg δ,RootedRestriction.prepare,List.map_ofFn] using hb.2
      have hr:=ops.dot_list k₀ c₀ bs hb.1 _ hy
      refine ⟨hr.1,hr.2.trans ?_⟩
      simpa only [MultiGraph.atRoot_restricted,hd₀] using (h₀ g ⟨hg,hp⟩ ⟨0,hn'⟩).symm

end PlanarHom.FixedRealOrientation
