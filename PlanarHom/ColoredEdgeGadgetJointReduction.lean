import PlanarHom.EdgeGadgetTemplateGeometry
import PlanarHom.PlanarGadgetInsertion

/-! NEW literal colored-template support for the recovered retained-context
APPEND compiler. Actual network reduction is constructed separately. This module
provides exact signature identities and ordinary outer-face geometry, not a
supplied oracle reduction or recovery of the entire missing historical module. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedGadgetNetwork
open Complexity
variable {b p e bt ut : ℕ} {C R : Type} [Fintype C] [CommSemiring R]

theorem ofColoredFinGraph_factor (G : MultiGraph (Fin b⊕Fin p) (Fin e)) (label : Fin e→Fin bt)
    (M : Fin bt→Matrix C C R) (U : Fin ut→C→R) (τ : Fin b→C) (η : Fin p→C) :
    factor (ofColoredFinGraph G label).code M U (mergeColor τ η) =
      ∏ i,M (label i) (Sum.elim τ η (G.src i)) (Sum.elim τ η (G.dst i)) := by
  have he (i : Fin e) : MixedCode.binaryValue (b+p) bt M (mergeColor τ η)
      ((finSumFinEquiv (G.src i)).val,(finSumFinEquiv (G.dst i)).val,(label i).val) =
      M (label i) (Sum.elim τ η (G.src i)) (Sum.elim τ η (G.dst i)) := by
    simp only [MixedCode.binaryValue,(finSumFinEquiv (G.src i)).isLt,
      (finSumFinEquiv (G.dst i)).isLt,(label i).isLt,and_self,↓reduceDIte]
    simp [mergeColor]
  simp only [factor,ofColoredFinGraph,Template.code,List.map_ofFn,List.prod_ofFn,
    Function.comp_def,he,List.map_nil,List.prod_nil,mul_one]

theorem ofColoredTwoTerminal_signature (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e→Fin bt) (M : Fin bt→Matrix C C R) (U : Fin ut→C→R) (τ : Fin 2→C) :
    templateSignature (ofColoredTwoTerminal G label) M U τ =
      TwoTerminal.coloredSignature G (fun k=>M (label k)) (fun _=>1) (τ 0) (τ 1) := by
  unfold templateSignature TwoTerminal.coloredSignature
  refine Finset.sum_bij (fun η _=>η) (by intro η _; simp)
    (fun _ _ _ _ h=>h) (by intro η _; exact ⟨η,by simp,rfl⟩) ?_
  intro η _
  change factor (ofColoredFinGraph (twoTerminalFinGraph G) label).code M U (mergeColor τ η) = _
  rw [ofColoredFinGraph_factor]
  simp only [Finset.prod_const_one,one_mul]
  apply Finset.prod_congr rfl
  intro k _
  have hc (z : Bool⊕Fin p) :
      Sum.elim τ η ((Equiv.sumCongr finTwoEquiv.symm (Equiv.refl _)) z) =
        TwoTerminal.extend (τ 0) (τ 1) η z := by
    rcases z with (z|z)
    · cases z <;> rfl
    · rfl
  exact congrArg₂ (M (label k)) (hc (G.src k)) (hc (G.dst k))

def singleFinEdge : TwoTerminal (Fin 0) (Fin 1) := ⟨fun _=>.inl false,fun _=>.inl true⟩

theorem singleFinEdge_planar : TwoTerminal.PlanarEdgeGadget singleFinEdge := by
  have h := TwoTerminal.reindexInternal_planar TwoTerminal.singleEdge
    (Fintype.equivFin Empty) (Fintype.equivFin PUnit)
    TwoTerminal.StripDrawing.singleEdge.planarEdgeGadget
  exact h

@[simp] theorem singleFinEdge_signature (M : Matrix C C R) (w : C→R) :
    TwoTerminal.coloredSignature singleFinEdge (fun _:Fin 1=>M) w = M := by
  funext i j
  simp [TwoTerminal.coloredSignature,singleFinEdge,TwoTerminal.extend]

end PlanarHom.FixedGadgetNetwork
namespace PlanarHom.EdgeSubstitution
open FixedGadgetNetwork
variable {C R : Type} [Fintype C] [CommSemiring R] {bt ut p e : ℕ}

def templateInteraction (t : Template) (M : Fin bt→Matrix C C R) (U : Fin ut→C→R) : Matrix C C R :=
  fun i j=>templateSignature t M U (fun v=>if v.val=0 then i else j)

def interactions (ts : List Template) (M : Fin bt→Matrix C C R) (U : Fin ut→C→R) :
    Fin ts.length→Matrix C C R := fun l=>templateInteraction (ts.get l) M U

theorem templateInteraction_colored (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e→Fin bt)
    (M : Fin bt→Matrix C C R) (U : Fin ut→C→R) :
    templateInteraction (ofColoredTwoTerminal G label) M U =
      TwoTerminal.coloredSignature G (fun k=>M (label k)) (fun _=>1) := by
  funext i j
  unfold templateInteraction
  rw [ofColoredTwoTerminal_signature]
  rfl

end PlanarHom.EdgeSubstitution
