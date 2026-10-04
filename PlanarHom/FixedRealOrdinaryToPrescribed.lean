import PlanarHom.FixedRealOrientationReduction
import PlanarHom.FixedRealListSum
import PlanarHom.ComputedBipartiteSideSemantics

/-! Actual ordinary-to-prescribed bipartite reduction: query both computed
orientations of every connected component, add their answers, and multiply
components. The two orientation values are never assumed equal. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealOrdinaryToPrescribed
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open PrescribedDomains HomogeneousSourceOrientation ComputedBipartiteSideQueries FixedRealRootRestrictions
variable {n e:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def connectedForward (M:Matrix C C K) (w:C→K) (side:C→Bool)
    (hcross:∀i j,M i j≠0→side i≠side j) :
    Reduction (FixedRealComponents.connectedProblem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w)
      (FixedRealOrientation.problem basis M w side) := by
  let prep:MixedCode→ℕ×List MixedCode:=fun g=>(0,queries g)
  let recov:ℕ×List (Code n e)→Code n e:=fun p=>sumList n e p.2
  have hp:FP MixedCode.encoding (BitEncoding.nat.prod MixedCode.encoding.list) prep:=
    (fp_const _ _ 0).pair fp_queries
  have hr:FP (BitEncoding.nat.prod (encoding n e).list) (encoding n e) recov:=
    (PairProjectionMachines.fp_snd _ _).comp (fp_sumList n e)
  apply presentationPipeline (presentation basis) (presentation basis) MixedCode.encoding BitEncoding.nat
    MixedCode.encoding MixedCode.normalizer BitEncoding.natNormalizer
    (FixedRealComponents.connectedValid (b:=1) (u:=0)) (EncodedGraph sidePolicies emptyPolicies)
    (totalEvaluation (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w)
    (totalEvaluation (fun _:Fin 1=>M) (extendedUnaries (fun u:Fin 0=>u.elim0) (Bipartite.domains side)) w)
    prep recov hp hr
  · intro g hg query hq
    cases h:(BipartiteRankTwoTractability.coloring g).1
    · simp [prep,queries,h] at hq
    · simp only [prep,queries,h,ite_true,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl <;> exact query_planar g hg.1 h _
  · intro g hg bs hbs
    have hb:=FixedRealComponents.represented_answers basis (queries g) bs _ hbs
    refine ⟨sumList_valid bs hb.1,?_⟩
    change value basis (sumList n e bs)=_
    rw [value_sumList basis bs hb.1,hb.2,totalEvaluation_valid _ _ _ g hg.1.1]
    exact queries_value_sum g hg.1.1 hg.2.1 hg.2.2 M w side hcross

def forward (M:Matrix C C K) (w:C→K) (side:C→Bool)
    (hcross:∀i j,M i j≠0→side i≠side j) :
    Reduction (FixedRealComponents.problem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w)
      (FixedRealOrientation.problem basis M w side) :=
  (FixedRealComponents.componentReduction basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w).trans
    (connectedForward basis M w side hcross)

end PlanarHom.FixedRealOrdinaryToPrescribed
