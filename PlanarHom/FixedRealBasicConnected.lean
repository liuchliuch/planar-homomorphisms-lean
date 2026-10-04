import PlanarHom.FixedRealBasicComponentMachines

/-! NEW checked connected evaluators for each literal basic zero-one block,
including zero blocks, isolates, and both complete-bipartite orientations. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealBasicComponents
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open PairProjectionMachines ZeroOneBasicTractability GraphComponentCode
variable {n e:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

structure ConnectedComputer (M:Matrix C C K) (w:C→K) where
  run : MixedCode→Code n e
  fp : FP MixedCode.encoding (encoding n e) run
  valid : ∀g,Valid n (run g)
  correct : ∀g,∀hg:g.Valid 1 0,(support g).Connected→0<g.vertices→
    value basis (run g)=g.evaluate hg (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w

theorem basic_computer (M:Matrix C C K) (w:C→K) (h:FieldBasicZeroOneComponent M) :
    Nonempty (ConnectedComputer basis M w) := by
  letI : Algebra ℚ K := ((algebraMap (RationalFunction n) K).comp
    (DenseRationalConstantExtraction.constantMap n)).toAlgebra
  rcases h with ⟨hne,hone⟩|⟨side,hsurj,hside⟩|⟨hne,hsub,hzero⟩
  · refine ⟨⟨(fun g=>powerCode basis (∑i,w i) g.vertices),
      MixedCode.fp_vertices.comp (fp_powerCode basis _),
      (fun g=>powerCode_valid basis _ _),?_⟩⟩
    intro g hg hc hn
    rw [powerCode_value,evaluate_homogeneous]
    have hm:M=(fun _ _=>1):=by funext i j;exact hone i j
    rw [hm,MultiGraph.partition_allOnes]
    simp
  · let μ:=fun i=>w ((sideFinEquiv side).symm (.inl i))
    let ν:=fun i=>w ((sideFinEquiv side).symm (.inr i))
    refine ⟨⟨bipartiteCode basis μ ν,fp_bipartiteCode basis μ ν,bipartiteCode_valid basis μ ν,?_⟩⟩
    intro g hg hc hn
    rw [bipartiteCode_value]
    have hm:M=bipartiteMatrix side:=by funext i j;exact hside i j
    rw [hm]
    exact connectedValue_eq side w g hg hc hn
  · let run:=fun g:MixedCode=>if g.edges=[] then powerCode basis (∑i,w i) g.vertices else constCode basis 0
    have hb:FP MixedCode.encoding BitEncoding.bool (fun g=>decide (g.edges=[])) := by
      have hl:=MixedCode.fp_edges.comp (ListCodecMachines.fp_length BipartiteRankTwoTractability.edgeCode)
      have he:=(hl.pair (fp_const _ BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
      exact he.congr (fun g=>by simp)
    have hf:FP MixedCode.encoding (encoding n e) run :=
      hb.ite (MixedCode.fp_vertices.comp (fp_powerCode basis _)) (fp_const _ _ (constCode basis 0))
    refine ⟨⟨run,hf,?_,?_⟩⟩
    · intro g
      dsimp only [run]
      split
      · exact powerCode_valid basis _ _
      · exact constant_valid basis _
    · intro g hg hc hn
      rw [hzero,evaluate_homogeneous]
      by_cases he:g.edges=[]
      · have hz:g.edges.length=0:=by simp [he]
        letI : IsEmpty (Fin g.edges.length) := ⟨fun i=>by have hh:=i.isLt;omega⟩
        simp only [run,if_pos he,powerCode_value]
        rw [MultiGraph.partition_edgeless]
        simp
      · have hp:0<g.edges.length:=List.length_pos_iff.mpr he
        letI : Nonempty (Fin g.edges.length) := ⟨⟨0,hp⟩⟩
        simp only [run,if_neg he,constant_value]
        exact (MultiGraph.partition_zero_of_nonempty_edges (g.toMultiGraph hg) w).symm

end PlanarHom.FixedRealBasicComponents
