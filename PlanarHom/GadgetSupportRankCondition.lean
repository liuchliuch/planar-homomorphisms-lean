import PlanarHom.SupportRankBlockMachines
import PlanarHom.TensorColorAutomorphisms
import PlanarHom.RootedRealTractability
import PlanarHom.MainDichotomyFinalAssembly

/-! NEW literal support-component rank condition of Proposition 2.5(ii).
The separating premise continues to quantify actual planar cofacial gadgets;
all source algorithms and hardness transfers use the original field codec. -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical
namespace PlanarHom.GadgetDiagonalSeparation
open Structures RootedRestriction Complexity Complexity.MixedCode
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
variable {C:Type} [Fintype C]

 theorem BasicBlock.rankBlock {M:Matrix C C ℝ} (h:BasicBlock M) : RankBlock M := by
  cases h with
  | zero e hm =>
    left
    have he:M=0:=funext (fun i=>funext (hm i))
    rw [he,Matrix.rank_zero]
  | positive k hk a ha e hm =>
    right;left
    have he:M=Matrix.vecMulVec (fun i=>a (e i)) (fun i=>a (e i)):=funext (fun i=>funext (hm i))
    have hu:M.rank≤1:=he ▸ Matrix.rank_vecMulVec_le (fun i=>a (e i)) (fun i=>a (e i))
    let r:C:=e.symm ⟨0,hk⟩
    have hl:0<M.rank:=rank_pos_of_entry_ne_zero M r r (by rw [hm];exact mul_ne_zero (ha _).ne' (ha _).ne')
    omega
  | bipartite k l hk hl a b ha hb e hm =>
    right;right
    let V:Matrix (Fin k) (Fin l) ℝ:=Matrix.vecMulVec a b
    have hu:V.rank≤1:=Matrix.rank_vecMulVec_le a b
    have hv:0<V.rank:=rank_pos_of_entry_ne_zero V ⟨0,hk⟩ ⟨0,hl⟩
      (mul_ne_zero (ha _).ne' (hb _).ne')
    refine ⟨k,l,V,e,by omega,?_⟩
    intro i j
    rw [hm]
    cases e i <;> cases e j <;> rfl

 def SupportRankCondition (M:Matrix C C ℝ) (hs:∀i j,M i j=M j i) : Prop :=
  ∀c:(colorSupport M hs).ConnectedComponent,RankBlock (fun i j:c.supp=>M i.val j.val)

 theorem Rigid.supportComponent {M:Matrix C C ℝ} (h:Rigid M) (hs:∀i j,M i j=M j i)
    (c:(colorSupport M hs).ConnectedComponent) : Rigid (fun i j:c.supp=>M i.val j.val) := by
  let G:=colorSupport M hs
  apply h.fiber G.connectedComponentMk c
  intro i j hij
  by_contra hn
  by_cases he:i=j
  · exact hij (congrArg G.connectedComponentMk he)
  · exact hij (SimpleGraph.ConnectedComponent.sound (show G.Adj i j from ⟨he,hn⟩).reachable)

 variable {q:ℕ}

 theorem subset_rank_inFP (L:RealLanguage q 1 0) (X:Set (Fin q)) (hunit:∀i,L.weights i=1)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (h:RankBlock (fun i j:X=>L.matrices 0 i.val j.val)) :
    (L.supportRestrictionProblem X).InFP := by
  have hf:=rankBlock_inFP L.field L.basis (fun i j:X=>L.matricesK 0 i.val j.val)
    (fun i j=>hs i.val j.val) h.changeFintype
  have hw:(fun i:X=>L.weightsK i.val)=(fun _=>1):=by
    funext i
    exact Subtype.ext (hunit i.val)
  change (evaluationProblem L.basis (fun _:Fin 1=>fun i j:X=>L.matricesK 0 i.val j.val)
    (fun u:Fin 0=>u.elim0) (fun i:X=>L.weightsK i.val)).InFP
  rw [hw]
  exact hf

 theorem support_rank_inFP (L:RealLanguage q 1 0) (hunit:∀i,L.weights i=1)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i) (h:SupportRankCondition (L.matrices 0) hs) :
    L.problem.InFP := by
  apply L.lemma35_inFP hs
  intro c
  exact subset_rank_inFP L c.supp hunit hs (h c).changeFintype

 theorem support_rank_of_not_hard_of_potts (hPotts:PositivePottsFoundation) (L:RealLanguage q 1 0)
    (hunit:∀i,L.weights i=1) (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn:∀i j,0≤L.matrices 0 i j) (hsep:Separates (L.matrices 0))
    (hnot:¬PromisedSharpPHard L.problem) : SupportRankCondition (L.matrices 0) hs := by
  have hb:=L.main_support_blocks_of_rectangular_source_of_potts hPotts
    (RectangularUnweightedSourceForms.source_language_form_of_not_hard_of_potts hPotts) hunit hs hnn hnot
  intro c
  exact (allowedBlock_basic_of_rigid (hb c) (hsep.rigid.supportComponent hs c)).rankBlock.changeFintype

 theorem proposition25ii_of_potts (hPotts:PositivePottsFoundation) (L:RealLanguage q 1 0)
    (hunit:∀i,L.weights i=1) (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn:∀i j,0≤L.matrices 0 i j) (hsep:Separates (L.matrices 0)) :
    (SupportRankCondition (L.matrices 0) hs→L.problem.InFP) ∧
      (¬SupportRankCondition (L.matrices 0) hs→PromisedSharpPHard L.problem) := by
  refine ⟨support_rank_inFP L hunit hs,?_⟩
  intro hbad
  by_contra hnot
  exact hbad (support_rank_of_not_hard_of_potts hPotts L hunit hs hnn hsep hnot)

end PlanarHom.GadgetDiagonalSeparation
