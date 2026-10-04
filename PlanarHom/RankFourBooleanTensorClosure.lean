import PlanarHom.RankFourBooleanTensorClass

noncomputable section
open Classical
namespace PlanarHom.RankFour
open Structures Boolean

theorem BooleanNormal.product_class {A B:Matrix Bool Bool ℝ}
    (hA:BooleanNormal A) (hB:BooleanNormal B) : NonnegativeClass (factorProduct A B) := by
  have hAc:=hA.nonnegativeClass
  have hBc:=hB.nonnegativeClass
  cases hA with
  | diagonal a c ha hc hm=>
    have he : A=(fun i j=>if i=j then (if i then c else a) else 0) := funext (fun i=>funext (hm i))
    rw [he]; exact diagonal_product_class a c ha hc B hBc
  | swap γ hγ hm=>
    have he : A=(fun i j=>γ*RankFour.swap i j) := funext (fun i=>funext (hm i))
    rw [he]
    cases hB with
    | diagonal a c ha hc hm=>
      have heB : B=(fun i j=>if i=j then (if i then c else a) else 0) := funext (fun i=>funext (hm i))
      rw [heB]
      exact product_comm_class _ _ (diagonal_product_class a c ha hc _ (swap_class γ hγ))
    | swap δ hδ hm=>
      have heB : B=(fun i j=>δ*RankFour.swap i j) := funext (fun i=>funext (hm i))
      rw [heB]; exact swap_swap_class γ δ hγ hδ
    | ising δ ρ hδ hρ hm=>
      have heB : B=(fun i j=>δ*W ρ i j) := funext (fun i=>funext (hm i))
      rw [heB]; exact swap_ising_class γ δ ρ hγ hδ hρ
  | ising γ ρ hγ hρ hm=>
    have he : A=(fun i j=>γ*W ρ i j) := funext (fun i=>funext (hm i))
    rw [he]
    cases hB with
    | diagonal a c ha hc hm=>
      have heB : B=(fun i j=>if i=j then (if i then c else a) else 0) := funext (fun i=>funext (hm i))
      rw [heB]
      exact product_comm_class _ _ (diagonal_product_class a c ha hc _ (ising_class γ ρ hγ hρ))
    | swap δ hδ hm=>
      have heB : B=(fun i j=>δ*RankFour.swap i j) := funext (fun i=>funext (hm i))
      rw [heB]; exact product_comm_class _ _ (swap_ising_class δ γ ρ hδ hγ hρ)
    | ising δ σ hδ hσ hm=>
      have heB : B=(fun i j=>δ*W σ i j) := funext (fun i=>funext (hm i))
      rw [heB]; exact ising_ising_class γ δ ρ σ hγ hδ hρ hσ

/-- The literal tensor alternative in Theorem 2.4, with equation (2.3). -/
def BooleanTensorClass {C:Type} (M:Matrix C C ℝ) : Prop :=
  ∃(A B:Matrix Bool Bool ℝ)(e:C≃Bool×Bool),BooleanEasy A ∧ BooleanEasy B ∧
    ∀i j,M i j=factorProduct A B (e i) (e j)

theorem BooleanTensorClass.nonnegativeClass {C:Type} [Fintype C]
    {M:Matrix C C ℝ} (hr:M.rank=Fintype.card C) (h:BooleanTensorClass M) :
    NonnegativeClass M := by
  obtain ⟨A,B,e,hA,hB,hm⟩:=h
  have hi:=rows_independent hr
  have hnA:=tensor_factor_not_rankOne hi A B hA.1 e hm
  have hnB:=tensor_factor_not_rankOne hi B A hB.1 (e.trans (Equiv.prodComm _ _)) (by
    intro i j; rw [hm]; exact mul_comm _ _)
  have hh:=(boolean_normal hA hnA).product_class (boolean_normal hB hnB)
  have hh':=hh.equiv e
  have he : M=(fun i j=>factorProduct A B (e i) (e j)) := funext (fun i=>funext (hm i))
  rwa [he]

theorem W_easy (γ ρ:ℝ) (hγ:0<γ) (hρ:0<ρ) : BooleanEasy (fun i j=>γ*W ρ i j) := by
  refine ⟨?_,?_,Or.inr (Or.inr ?_)⟩
  · intro i j; dsimp only; rw [W_symm]
  · intro i j; exact (mul_pos hγ (W_pos hρ _ _)).le
  · simp

theorem swap_easy (γ:ℝ) (hγ:0<γ) : BooleanEasy (fun i j=>γ*RankFour.swap i j) := by
  refine ⟨?_,?_,Or.inr (Or.inr ?_)⟩
  · intro i j; simp [swap,eq_comm]
  · intro i j; cases i <;> cases j <;> simp [swap,hγ.le]
  · simp [swap]

theorem SingleTensor.booleanTensorClass {C:Type} {M:Matrix C C ℝ} (h:SingleTensor M) :
    BooleanTensorClass M := by
  rcases h with ⟨γ,ρ,e,hγ,hρ,hm⟩|⟨γ,ρ,e,hγ,hρ,hm⟩
  · refine ⟨(fun i j=>γ*W (ρ 0) i j),W (ρ 1),e.trans (finTwoArrowEquiv Bool),
      W_easy γ (ρ 0) hγ (hρ 0),?_,?_⟩
    · simpa only [one_mul] using W_easy 1 (ρ 1) (by norm_num) (hρ 1)
    · intro i j; rw [hm]; simp [factorProduct,tensor,Fin.prod_univ_two,finTwoArrowEquiv]; ring
  · refine ⟨(fun i j=>γ*RankFour.swap i j),W ρ,e,swap_easy γ hγ,?_,?_⟩
    · simpa only [one_mul] using W_easy 1 ρ (by norm_num) hρ
    · intro i j; exact hm i j

end PlanarHom.RankFour
