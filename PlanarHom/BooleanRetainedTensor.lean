import PlanarHom.TractableEvaluation
import PlanarHom.PottsRandomCluster
import PlanarHom.CubeTensorExponential
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Exact removal of identity tensor factors in Theorem5.1, including all
isolated input vertices. The final unique-root statement is mathematical only;
no root-extraction algorithm is supplied by this identity. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanRetainedTensor
variable {V E : Type} [Fintype V] [Fintype E]

/-- Every input component, including an isolate, independently chooses a color. -/
theorem unweighted_identity {C R : Type} [Fintype C] [DecidableEq C] [CommSemiring R]
    (G : MultiGraph V E) : G.unweighted (1 : Matrix C C R)=
      (Fintype.card C : R)^(G.componentCount Finset.univ) := by
  rw [MultiGraph.unweighted_eq,←G.sum_edgeIndicator (C:=C) (R:=R) Finset.univ]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.prod_congr rfl
  intro e _
  rw [Matrix.one_apply]
  by_cases h:σ (G.src e)=σ (G.dst e) <;> simp [h]

def retained {d : ℕ} (S : Finset (Fin d)) (B : Matrix Bool Bool ℝ) : Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ:=
  CubeTensorExponential.tensor (fun r=>if r∈S then B else 1)

theorem partition_retained {d : ℕ} (G : MultiGraph V E) (S : Finset (Fin d)) (B : Matrix Bool Bool ℝ) :
    G.unweighted (retained S B)=
      (2 : ℝ)^((d-S.card)*G.componentCount Finset.univ)*(G.unweighted B)^S.card := by
  rw [show retained S B=(fun x y=>∏r : Fin d,(if r∈S then B else 1) (x r) (y r)) from rfl]
  rw [G.unweighted_piInteraction]
  have hf : (fun r : Fin d=>G.unweighted (if r∈S then B else 1))=
      (fun r=>if r∈S then G.unweighted B else G.unweighted (1 : Matrix Bool Bool ℝ)) := by
    funext r
    split <;> rfl
  rw [hf,Finset.prod_ite]
  simp only [Finset.filter_univ_mem,Finset.prod_const]
  have hfilter : Finset.univ.filter (fun r : Fin d=>r∉S)=Sᶜ := by ext r; simp
  rw [hfilter,Finset.card_compl,Fintype.card_fin]
  rw [unweighted_identity (C:=Bool),Fintype.card_bool,←pow_mul]
  rw [Nat.mul_comm (G.componentCount Finset.univ)]
  norm_num only [Nat.cast_ofNat]
  ring

theorem unweighted_pos (G : MultiGraph V E) (B : Matrix Bool Bool ℝ)
    (hB : ∀i j,0<B i j) : 0<G.unweighted B := by
  rw [MultiGraph.unweighted_eq]
  exact Finset.sum_pos (fun _ _=>Finset.prod_pos (fun _ _=>hB _ _)) Finset.univ_nonempty

/-- The known component factor leaves exactly the fixed power to be recovered. -/
theorem normalized_value {d : ℕ} (G : MultiGraph V E) (S : Finset (Fin d)) (B : Matrix Bool Bool ℝ) :
    G.unweighted (retained S B)/(2 : ℝ)^((d-S.card)*G.componentCount Finset.univ)=
      (G.unweighted B)^S.card := by
  rw [partition_retained]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num))

/-- Uniqueness uses positivity and the actual nonempty retained coordinate set.
This is not a polynomial-time root oracle. -/
theorem unique_positive_root {d : ℕ} (G : MultiGraph V E) (S : Finset (Fin d))
    (hS : S.Nonempty) (B : Matrix Bool Bool ℝ) (hB : ∀i j,0<B i j) :
    ∃!z : ℝ,0<z ∧ z^S.card=
      G.unweighted (retained S B)/(2 : ℝ)^((d-S.card)*G.componentCount Finset.univ) := by
  refine ⟨G.unweighted B,⟨unweighted_pos G B hB,(normalized_value G S B).symm⟩,?_⟩
  intro z hz
  exact (pow_left_inj₀ hz.1.le (unweighted_pos G B hB).le (Nat.ne_of_gt hS.card_pos)).mp
    (hz.2.trans (normalized_value G S B))

end PlanarHom.BooleanRetainedTensor
