import PlanarHom.BipartiteRankTwoEvaluationMachines
import PlanarHom.RankOneEvaluationMachine
import PlanarHom.SupportBlockSemantics
import PlanarHom.ZeroOneBasicStructure

/-! NEW all-valid-input programs for literal looped cliques, complete
bipartite targets and zero singleton blocks, with arbitrary fixed weights. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.ZeroOneBasicTractability
open Complexity Complexity.MixedCode GraphComponentCode
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K] {dimension : ℕ}

def FieldBasicZeroOneComponent (M : Matrix C C K) : Prop :=
  (Nonempty C ∧ ∀i j,M i j=1) ∨
  (∃side : C→Bool,Function.Surjective side ∧ ∀i j,M i j=if side i=side j then 0 else 1) ∨
  (Nonempty C ∧ Subsingleton C ∧ M=0)

def bipartiteMatrix (side : C→Bool) : Matrix C C K := fun i j=>if side i=side j then 0 else 1

def sideEquiv (side : C→Bool) : C≃{c // side c=false}⊕{c // side c=true} where
  toFun c:=if h:side c=false then .inl ⟨c,h⟩ else .inr ⟨c,by cases hs:side c <;> simp_all⟩
  invFun:=Sum.elim Subtype.val Subtype.val
  left_inv c:=by dsimp only; split <;> rfl
  right_inv p:=by
    rcases p with ⟨c,h⟩|⟨c,h⟩ <;> simp [h]

def sideFinEquiv (side : C→Bool) : C≃Fin (Fintype.card {c // side c=false})⊕Fin (Fintype.card {c // side c=true}) :=
  (sideEquiv side).trans (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))

theorem sideFinEquiv_left (side : C→Bool) (i : Fin (Fintype.card {c // side c=false})) :
    side ((sideFinEquiv side).symm (.inl i))=false :=
  ((Fintype.equivFin {c // side c=false}).symm i).property

theorem sideFinEquiv_right (side : C→Bool) (i : Fin (Fintype.card {c // side c=true})) :
    side ((sideFinEquiv side).symm (.inr i))=true :=
  ((Fintype.equivFin {c // side c=true}).symm i).property

def connectedValue (side : C→Bool) (w : C→K) : MixedCode→K :=
  BipartiteRankTwoTractability.evaluateConnected
    (fun _ : Fin (Fintype.card {c // side c=false})=>1)
    (fun i=>w ((sideFinEquiv side).symm (.inl i)))
    (fun _ : Fin (Fintype.card {c // side c=true})=>1)
    (fun i=>w ((sideFinEquiv side).symm (.inr i)))

theorem fp_connectedValue (basis : Module.Basis (Fin dimension) ℚ K) (side : C→Bool) (w : C→K) :
    FP encoding (numberFieldEncoding basis) (connectedValue side w) :=
  BipartiteRankTwoTractability.fp_evaluateConnected basis _ _ _ _

theorem connectedValue_eq (side : C→Bool) (w : C→K) (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (support g).Connected) (hn : 0<g.vertices) :
    connectedValue side w g=g.evaluate hg (fun _ : Fin 1=>bipartiteMatrix side)
      (fun u : Fin 0=>u.elim0) w := by
  let e:=sideFinEquiv side
  have hm : (fun i j=>bipartiteMatrix (K:=K) side (e.symm i) (e.symm j))=
      BipartiteRankTwoTractability.matrix (fun _=>1) (fun _=>1) := by
    funext i j
    cases i <;> cases j <;>
      simp [e,bipartiteMatrix,sideFinEquiv_left,sideFinEquiv_right,BipartiteRankTwoTractability.matrix]
  have hw : Sum.elim (fun i=>w (e.symm (.inl i))) (fun i=>w (e.symm (.inr i)))=(fun i=>w (e.symm i)) := by
    funext i
    cases i <;> rfl
  unfold connectedValue
  rw [BipartiteRankTwoTractability.evaluateConnected_correct g hg hc hn,
    evaluate_homogeneous,evaluate_homogeneous,hw,←hm]
  exact (g.toMultiGraph hg).partition_reindexColors (bipartiteMatrix side) w e.symm

def evaluateCode (side : C→Bool) (w : C→K) (g : MixedCode) : K :=
  ((components g).map (connectedValue side w)).prod

theorem fp_evaluateCode (basis : Module.Basis (Fin dimension) ℚ K) (side : C→Bool) (w : C→K) :
    FP encoding (numberFieldEncoding basis) (evaluateCode side w) :=
  (GraphComponentMachines.fp_components.comp
    (ListMapMachines.fp_map _ _ _ (fp_connectedValue basis side w))).comp
      (MaterializedFieldListMachines.fp_product basis)

end PlanarHom.ZeroOneBasicTractability
