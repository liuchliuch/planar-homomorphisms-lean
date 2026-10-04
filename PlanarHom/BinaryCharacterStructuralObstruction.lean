import PlanarHom.BinaryCharacterExponential
import PlanarHom.InjectiveWeightedStructuralTransfer
import PlanarHom.CenteredLogStructural

noncomputable section
open Classical
namespace PlanarHom.BinaryCharacters
open Structures CenteredLogTensorExpansion
variable {X:Type} [AddCommGroup X] [Module F₂ X] [Fintype X] {m:ℕ}

theorem reindex_product {Y:Type} [Fintype Y] (e:X≃Y) (A B:Matrix X X ℝ) :
    Matrix.reindex e e (A*B)=Matrix.reindex e e A*Matrix.reindex e e B := by
  ext x y
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.mul_apply]
  apply Fintype.sum_equiv e
  intro i
  simp only [Equiv.symm_apply_apply]

theorem reindex_centering (e:X≃Fin (Fintype.card X)) :
    Matrix.reindex e e (centering X)=sourceCentering (Fintype.card X) := by
  ext x y
  simp [centering,ones,sourceCentering,sourceOnes,Matrix.reindex_apply,Matrix.submatrix_apply,
    Matrix.one_apply,e.symm.injective.eq_iff]

def codedInteraction (l:Fin m→X→ₗ[F₂]F₂) (J:Fin m→ℝ) :
    Matrix (Fin (Fintype.card X)) (Fin (Fintype.card X)) ℝ :=
  Matrix.reindex (Fintype.equivFin X) (Fintype.equivFin X) (interaction l J)

theorem coded_centered_log_rank (l:Fin m→X→ₗ[F₂]F₂) (hl:Function.Injective l)
    (hn:∀r,l r≠0) (J:Fin m→ℝ) (hJ:∀r,J r≠0) :
    (sourceCentering (Fintype.card X)*entrywiseLog (codedInteraction l J)*sourceCentering (Fintype.card X)).rank=m := by
  let e:=Fintype.equivFin X
  have he:entrywiseLog (codedInteraction l J)=Matrix.reindex e e (kernel l J) := by
    ext x y; simp [entrywiseLog,codedInteraction,interaction,e]
  have hh:=centered_kernel_rank l hl hn J hJ
  rw [←Matrix.rank_reindex e e] at hh
  simpa only [reindex_product,reindex_centering,←he] using hh

theorem structural_cardinality_and_weight (l:Fin m→X→ₗ[F₂]F₂) (hl:Function.Injective l)
    (hn:∀r,l r≠0) (hsep:∀x y,(∀r,l r x=l r y)→x=y)
    (J:Fin m→ℝ) (hJ:∀r,J r≠0) (w:X→ℝ) (hw:∀x,0 < w x)
    (h:WeightedClass (interaction l J) w) :
    Fintype.card X=2^m ∧ ∃μ:ℝ,0 < μ ∧ ∀x,w x=μ := by
  let q:=Fintype.card X
  let e:=Fintype.equivFin X
  let M:=codedInteraction l J
  let W:Fin q→ℝ:=fun x=>w (e.symm x)
  letI:Nonempty (Fin q):=⟨e 0⟩
  have hs:∀i j,M i j=M j i := by
    intro i j; exact interaction_symmetric l J _ _
  have hp:∀i j,0 < M i j := by intro i j; exact Real.exp_pos _
  have hd:∀i j,M i i=M j j := by
    intro i j
    exact (interaction_diagonal l J _).trans (interaction_diagonal l J _).symm
  have hi:Function.Injective M := by
    intro i j hh
    apply e.symm.injective
    apply hsep
    apply (equal_rows_iff l hl J hJ _ _).mp
    funext z
    have he:=congrFun hh (e z)
    simpa only [M,e,codedInteraction,Matrix.reindex_apply,Matrix.submatrix_apply,
      Equiv.symm_apply_apply] using he
  have hc:PositiveVertexWeightClass M W hs :=
    actual_membership_of_weightedClass M W hs hi (h.equiv e.symm)
  obtain ⟨d,ed,γ,μ,ρ,hqd,hγ,hμ,hρ,hM,hW,hr⟩:=
    CenteredLogStructural.lemma124_structure_and_rank M W hs hp hd hi (fun i=>hw _) hc
  have hm:(sourceCentering q*entrywiseLog M*sourceCentering q).rank=m:=coded_centered_log_rank l hl hn J hJ
  have hdm:d=m:=hr.symm.trans hm
  refine ⟨by simpa only [hdm] using hqd,μ,hμ,?_⟩
  intro x
  simpa only [W,Equiv.symm_apply_apply] using hW (e x)

end PlanarHom.BinaryCharacters
