import PlanarHom.PottsTutteIdentity
import PlanarHom.PottsCenteredPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots

/-! Literal two-variable random-cluster semantics, with separate exact edge and
color polynomials. These are derived from actual occurrence connectivity. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
open Polynomial
variable {V E : Type} [Fintype V] [Fintype E]

def randomCluster (G : MultiGraph V E) (Q v : ℚ) : ℚ :=
  ∑ A : Finset E,Q^G.componentCount A*v^A.card

def randomClusterEdgePolynomial (G : MultiGraph V E) (Q : ℚ) : Polynomial ℚ :=
  ∑ A : Finset E,C (Q^G.componentCount A)*X^A.card

def randomClusterColorPolynomial (G : MultiGraph V E) (v : ℚ) : Polynomial ℚ :=
  ∑ A : Finset E,C (v^A.card)*X^G.componentCount A

@[simp] theorem eval_randomClusterEdgePolynomial (G : MultiGraph V E) (Q v : ℚ) :
    (G.randomClusterEdgePolynomial Q).eval v=G.randomCluster Q v := by
  simp [randomClusterEdgePolynomial,randomCluster,eval_finset_sum]

@[simp] theorem eval_randomClusterColorPolynomial (G : MultiGraph V E) (Q v : ℚ) :
    (G.randomClusterColorPolynomial v).eval Q=G.randomCluster Q v := by
  simp [randomClusterColorPolynomial,randomCluster,eval_finset_sum,mul_comm]

theorem randomClusterEdgePolynomial_degree (G : MultiGraph V E) (Q : ℚ) :
    (G.randomClusterEdgePolynomial Q).natDegree≤Fintype.card E := by
  apply natDegree_sum_le_of_forall_le
  intro A _
  apply (natDegree_C_mul_le _ _).trans
  simpa using Finset.card_le_univ A

theorem randomClusterColorPolynomial_degree (G : MultiGraph V E) (v : ℚ) :
    (G.randomClusterColorPolynomial v).natDegree≤Fintype.card V := by
  apply natDegree_sum_le_of_forall_le
  intro A _
  apply (natDegree_C_mul_le _ _).trans
  simpa using G.componentCount_le_vertices A

theorem randomCluster_zero_color [Nonempty V] (G : MultiGraph V E) (v : ℚ) :
    G.randomCluster 0 v=0 := by
  apply Finset.sum_eq_zero
  intro A _
  letI : Nonempty (G.Components A) := ⟨Quotient.mk _ (Classical.arbitrary V)⟩
  have hp : 0<G.componentCount A := Fintype.card_pos
  simp [ne_of_gt hp]

theorem randomCluster_potts (G : MultiGraph V E) (q : ℕ) :
    G.randomCluster q 1=G.unweighted (ProperColoringPottsReduction.positivePottsMatrix q) := by
  have he : (ProperColoringPottsReduction.positivePottsMatrix q : Matrix (Fin q) (Fin q) ℚ)=
      pottsInteraction := by
    funext i j
    by_cases h : i=j <;> norm_num [ProperColoringPottsReduction.positivePottsMatrix,pottsInteraction,h]
  rw [he,unweighted,potts_randomCluster]
  simp [randomCluster]

/-- Weighted FK expansion at every finite color cardinality. -/
theorem weighted_randomCluster (G : MultiGraph V E) (q : ℕ) (v : ℚ) :
    G.unweighted (fun (i j : Fin q) => (if i=j then v else 0)+1)=
      G.randomCluster q v := by
  rw [unweighted_eq]
  simp_rw [Finset.prod_add_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  have hw (σ : V → Fin q) :
      (∏ e∈A,if σ (G.src e)=σ (G.dst e) then v else 0)=
        v^A.card*(∏ e∈A,if σ (G.src e)=σ (G.dst e) then (1:ℚ) else 0) := by
    rw [← Finset.prod_const,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e _
    split_ifs <;> simp
  simp_rw [hw]
  rw [← Finset.mul_sum]
  calc
    _ = v^A.card*(Fintype.card (Fin q):ℚ)^G.componentCount A :=
      by
        convert congrArg (fun x : ℚ => v^A.card*x) (G.sum_edgeIndicator (C:=Fin q) (R:=ℚ) A) using 1
        congr 1
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.prod_congr rfl
        intro e _
        by_cases h : σ (G.src e)=σ (G.dst e) <;> simp [h]
    _ = _ := by simp [mul_comm]
end PlanarHom.MultiGraph
