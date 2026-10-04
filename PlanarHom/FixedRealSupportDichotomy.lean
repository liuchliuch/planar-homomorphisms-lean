import PlanarHom.FixedRealSupportHardness
import PlanarHom.FixedRealBasicSupportTractability

/-! NEW complete A.9 endpoint: nonbasic signed support is genuinely #P-hard,
while all three literal zero-one basic supports have actual represented FP
algorithms with arbitrary fixed positive real vertex weights. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealSupportHardness
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open FixedRealComponents RootedRestriction ZeroOneBasicStructure ZeroOneBasicTractability
variable {n e q:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K) (φ:K→+*ℝ)

def BasicSupport (M:Matrix (Fin q) (Fin q) K) (hs:∀i j,M i j=M j i) : Prop :=
  ∀c:(colorSupport (fun i j=>φ (M i j)) (fun i j=>congrArg φ (hs i j))).ConnectedComponent,
    BasicZeroOneComponent (fun i j:c.supp=>φ (M i.val j.val))

theorem basic_field (M:Matrix (Fin q) (Fin q) K) (hs:∀i j,M i j=M j i)
    (h:BasicSupport φ M hs) :
    ∀c:(colorSupport M hs).ConnectedComponent,
      FieldBasicZeroOneComponent (fun i j:c.supp=>M i.val j.val) := by
  have hg:colorSupport M hs=colorSupport (fun i j=>φ (M i j)) (fun i j=>congrArg φ (hs i j)) := by
    ext i j
    change (i≠j ∧ M i j≠0) ↔ (i≠j ∧ φ (M i j)≠0)
    simp only [map_ne_zero]
  rw [hg]
  intro c
  rcases h c with ⟨hne,hone⟩|⟨side,hsurj,hside⟩|⟨hne,hsub,hzero⟩
  · exact Or.inl ⟨hne,fun i j=>φ.injective (by simpa only [map_one] using hone i j)⟩
  · refine Or.inr (Or.inl ⟨side,hsurj,?_⟩)
    intro i j
    apply φ.injective
    simpa only [apply_ite,map_zero,map_one] using hside i j
  · refine Or.inr (Or.inr ⟨hne,hsub,?_⟩)
    funext i j
    apply φ.injective
    simpa using congrFun (congrFun hzero i) j

theorem theoremA9_basic_inFP (M:Matrix (Fin q) (Fin q) K) (hs:∀i j,M i j=M j i)
    (w:Fin q→K) (h:BasicSupport φ M hs) :
    (problem basis (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w).InFP :=
  FixedRealBasicComponents.basic_support_inFP basis M hs w (basic_field φ M hs h)

/-- The exact positive-real-weight extension of the zero-one dichotomy. -/
theorem theoremA9_zeroOne (M:Matrix (Fin q) (Fin q) K) (hs:∀i j,M i j=M j i)
    (w:Fin q→K) (hw:∀i,0<φ (w i)) (h01:∀i j,M i j=0 ∨ M i j=1) :
    (BasicSupport φ M hs→(problem basis (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w).InFP) ∧
    (¬BasicSupport φ M hs→RepresentedBit.SharpPHard
      (problem basis (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w)) := by
  refine ⟨theoremA9_basic_inFP basis φ M hs w,?_⟩
  intro hb
  by_contra hn
  exact hb (zeroOne_basic_of_not_hard basis φ M hs w hw h01 hn)

/-- The zero-matrix formula includes isolated vertices and the empty input,
without division by a partition value. -/
theorem zero_value (w:Fin q→K) (g:MixedCode) (hg:g.Valid 1 0) :
    totalEvaluation (fun _:Fin 1=>fun _:Fin q=>fun _:Fin q=>(0:K)) (fun i:Fin 0=>i.elim0) w g=
      if g.edges=[] then (∑i,w i)^g.vertices else 0 := by
  rw [totalEvaluation_valid _ _ _ g hg,evaluate_homogeneous]
  by_cases he:g.edges=[]
  · have hz:g.edges.length=0:=by simp [he]
    letI : IsEmpty (Fin g.edges.length) := ⟨fun i=>by have hi:=i.isLt;omega⟩
    rw [if_pos he,MultiGraph.partition_edgeless]
    simp
  · letI : Nonempty (Fin g.edges.length) := ⟨⟨0,List.length_pos_iff.mpr he⟩⟩
    rw [if_neg he]
    exact MultiGraph.partition_zero_of_nonempty_edges _ w

end PlanarHom.FixedRealSupportHardness
