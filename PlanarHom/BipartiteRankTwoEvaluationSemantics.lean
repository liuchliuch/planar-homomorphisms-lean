import PlanarHom.BipartiteRankTwoColoring
import PlanarHom.RankOneEvaluationMachine

/-! NEW exact connected-input evaluation of weighted bipartite rank-two
blocks. Both possible side orientations are summed, with original independent
amplitudes and masses. Isolated vertices are retained. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.BipartiteRankTwoTractability
open Complexity Complexity.MixedCode HomogeneousSourceOrientation
variable {k l : ℕ} {K : Type} [Field K]

def sideFactor (a μ : Fin k → K) (b ν : Fin l → K) (side : Bool) (degree : ℕ) : K :=
  if side then RankOneEvaluationMachine.factor b ν degree else RankOneEvaluationMachine.factor a μ degree

def sideProduct (g : MixedCode) (hg : g.Valid 1 0) (a μ : Fin k → K) (b ν : Fin l → K)
    (δ : ℕ → Bool) : K := ∏v : Fin g.vertices,sideFactor a μ b ν (δ v.val) ((g.toMultiGraph hg).degree v)

theorem matrix_eq_rankOne (a : Fin k → K) (b : Fin l → K) (i j : Fin k ⊕ Fin l)
    (h : side i≠side j) : matrix a b i j=Sum.elim a b i*Sum.elim a b j := by
  cases i <;> cases j <;> simp_all [matrix,side,mul_comm]

theorem rootRestricted_sideProduct (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (a μ : Fin k → K) (b ν : Fin l → K) (δ : ℕ → Bool) (hδ : Proper g δ) :
    (g.toMultiGraph hg).rootRestricted r (matrix a b) (Sum.elim μ ν)
      {i | side i=δ r.val} = sideProduct g hg a μ b ν δ := by
  rw [rootRestricted_eq_side_sum g hg hc r (matrix a b) (matrix_symmetric a b)
    (Sum.elim μ ν) side (matrix_crosses a b) (fun v=>δ v.val) (proper_support g hg δ hδ)]
  let G := g.toMultiGraph hg
  let A : Fin k ⊕ Fin l → K := Sum.elim a b
  let W : Fin k ⊕ Fin l → K := Sum.elim μ ν
  have hterm (σ : Fin g.vertices → Fin k ⊕ Fin l) :
      (if ∀v,side (σ v)=δ v.val then G.assignmentWeight (matrix a b) W σ else 0) =
        ∏v,if side (σ v)=δ v.val then W (σ v)*A (σ v)^G.degree v else 0 := by
    by_cases hs : ∀v,side (σ v)=δ v.val
    · rw [if_pos hs]
      simp only [hs,↓reduceIte]
      unfold MultiGraph.assignmentWeight
      have hedge : ∀e,matrix a b (σ (G.src e)) (σ (G.dst e))=A (σ (G.src e))*A (σ (G.dst e)) := by
        intro e
        apply matrix_eq_rankOne
        rw [hs,hs]
        exact hδ (g.edges.get e) (List.get_mem _ _)
      simp_rw [hedge]
      rw [←G.prod_pow_degree (fun v=>A (σ v)),Finset.prod_mul_distrib]
    · rw [if_neg hs]
      obtain ⟨v,hv⟩ := not_forall.mp hs
      exact (Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)).symm
  change (∑σ : Fin g.vertices → Fin k ⊕ Fin l,
    if ∀v,side (σ v)=δ v.val then G.assignmentWeight (matrix a b) W σ else 0)=_
  have heq : (∑σ : Fin g.vertices → Fin k ⊕ Fin l,
      if ∀v,side (σ v)=δ v.val then G.assignmentWeight (matrix a b) W σ else 0) =
      ∑σ : Fin g.vertices → Fin k ⊕ Fin l,
        ∏v,if side (σ v)=δ v.val then W (σ v)*A (σ v)^G.degree v else 0 := by
    apply Finset.sum_congr rfl
    intro σ _
    exact hterm σ
  rw [heq,←Fintype.prod_sum (fun (v : Fin g.vertices) (i : Fin k ⊕ Fin l) =>
    if side i=δ v.val then W i*A i^G.degree v else 0)]
  apply Finset.prod_congr rfl
  intro v _
  change (∑i : Fin k ⊕ Fin l, if side i=δ v.val then W i*A i^G.degree v else 0)=_
  rw [Fintype.sum_sum_type]
  cases hd : δ v.val <;> simp [sideFactor,side,W,A,RankOneEvaluationMachine.factor,hd,G]

theorem partition_two_orientations (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (a μ : Fin k → K) (b ν : Fin l → K) (δ : ℕ → Bool) (hδ : Proper g δ) :
    (g.toMultiGraph hg).partition (matrix a b) (Sum.elim μ ν) =
      sideProduct g hg a μ b ν δ + sideProduct g hg a μ b ν (fun v=>!(δ v)) := by
  have hsplit : (g.toMultiGraph hg).partition (matrix a b) (Sum.elim μ ν) =
      (g.toMultiGraph hg).rootRestricted r (matrix a b) (Sum.elim μ ν) {i | side i=δ r.val} +
      (g.toMultiGraph hg).rootRestricted r (matrix a b) (Sum.elim μ ν) {i | side i=!(δ r.val)} := by
    unfold MultiGraph.partition MultiGraph.rootRestricted
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    cases hs : side (σ r) <;> cases hd : δ r.val <;> simp [hs,hd]
  rw [hsplit,rootRestricted_sideProduct g hg hc r a μ b ν δ hδ,
    rootRestricted_sideProduct g hg hc r a μ b ν _ (proper_not g hδ)]

end PlanarHom.BipartiteRankTwoTractability
