import PlanarHom.CountingCookLevinReferenceWiring
import PlanarHom.CountingCookLevinIndexedBlocks

/-! Literal equality of the uniform materialized emitter and the proved shared
NOR layer compiler. No semantic-machine premise is substituted for the emitter. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic

def stateBlock (m : Machine) (C : ℕ) (p : RefInput)
    (out : StateBit m (p.1.length+p.2.1)) : NorGates :=
  (stepLayer m out).regularBlock C (timeStart m C p+4+4*C*stateOrdinal m out) (globalReference m C p)

theorem baseBlock_eq (m : Machine) (C : ℕ) (p : RefInput) (b : BaseStateBit m) :
    baseBlock m C b p=stateBlock m C p (.inl b) := by
  rcases b with q | (a | v)
  all_goals simpa only [baseBlock,stateBlock,stepLayer,stateOrdinal_base,timeStart_setCell,Fin.val_zero] using
    (numericLocalBlock_eq m C p false 0 _ (timeStart m C p+4+4*C*(Fintype.equivFin (BaseStateBit m) _).val))

theorem cellBlock_eq (m : Machine) (C : ℕ) (p : RefInput) (side : Bool)
    (i : Fin (p.1.length+p.2.1+1)) (a : Option m.Γ) :
    cellBlock m C side a (setCell p i.val)=stateBlock m C p (.inr (side,i,a)) := by
  simpa only [cellBlock,stateBlock,stepLayer,stateOrdinal_cell,timeStart_setCell,cellOrdinal_setCell,
    cellOrdinal,refWidth,setCell] using
    (numericLocalBlock_eq m C p side i (fun c => decide (localCell m c=a))
      (timeStart m C p+4+4*C*cellOrdinal m p side i.val a))

theorem regularLayer_stateOrder (m : Machine) (C : ℕ) (p : RefInput) :
    Expr.regularLayer ((stateRegisterOrder m (p.1.length+p.2.1)).map (stepLayer m)) C
      (timeStart m C p+4) (globalReference m C p)=
      (stateRegisterOrder m (p.1.length+p.2.1)).flatMap (stateBlock m C p) := by
  simp only [stateRegisterOrder,List.map_ofFn,Expr.regularLayer_ofFn,List.finRange,List.flatMap,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply,stateBlock,stateOrdinal,Equiv.apply_symm_apply]

theorem uniformStep_eq_layer (m : Machine) (C : ℕ) (p : RefInput) :
    uniformStep m C p = [(p.2.2.1,p.2.2.1)] ++
      Expr.regularLayer ((stateRegisterOrder m (p.1.length+p.2.1)).map (stepLayer m)) C
        (timeStart m C p+4) (globalReference m C p) := by
  rw [regularLayer_stateOrder,stateRegisterOrder_eq]
  simp only [uniformStep,List.flatMap_append,List.flatMap_map,List.flatMap_assoc,List.append_assoc]
  congr 1
  change baseLayer m C p ++ _ = _ ++ _
  congr 1
  · unfold baseLayer
    apply List.flatMap_congr
    intro b _
    exact baseBlock_eq m C p b
  · apply List.flatMap_congr
    intro side _
    unfold sideLayer
    rw [show refWidth p=p.1.length+p.2.1+1 from rfl,← List.map_coe_finRange,List.flatMap_map]
    apply List.flatMap_congr
    intro i _
    unfold cellRow
    apply List.flatMap_congr
    intro a _
    exact cellBlock_eq m C p side i a

end PlanarHom.CountingCookLevin
