import PlanarHom.CountingCookLevinUniformSizes
import Mathlib.Data.List.OfFn

noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic

/-- The emitter's nested loops enumerate the canonical arithmetic state slots. -/
theorem stateRegisterOrder_eq (m : Machine) (L : ℕ) :
    stateRegisterOrder m L =
      (fixedOrder (BaseStateBit m)).map Sum.inl ++
      (fixedOrder Bool).flatMap (fun side => (List.finRange (L+1)).flatMap
        (fun i => (fixedOrder (Option m.Γ)).map (fun a => Sum.inr (side,i,a)))) := by
  simp only [stateRegisterOrder,fixedOrder,List.flatMap,List.map_ofFn,List.finRange]
  rw [List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn
    funext i
    apply (stateIndexEquiv m L).injective
    simp only [Equiv.apply_symm_apply,Function.comp_apply]
    apply Fin.ext
    change i.val=(Fintype.equivFin (BaseStateBit m) ((Fintype.equivFin (BaseStateBit m)).symm i)).val
    simp
  · rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    apply congrArg List.ofFn
    funext k
    apply (stateIndexEquiv m L).injective
    simp only [Equiv.apply_symm_apply,Function.comp_apply]
    apply Fin.ext
    change Fintype.card (BaseStateBit m)+
      (i.val*((L+1)*Fintype.card (Option m.Γ))+(j.val*Fintype.card (Option m.Γ)+k.val)) =
      Fintype.card (BaseStateBit m)+
      ((Fintype.equivFin (Option m.Γ) ((Fintype.equivFin (Option m.Γ)).symm k)).val+
        Fintype.card (Option m.Γ)*j.val+
        ((L+1)*Fintype.card (Option m.Γ))*(Fintype.equivFin Bool ((Fintype.equivFin Bool).symm i)).val)
    simp only [Equiv.apply_symm_apply]
    ring

end PlanarHom.CountingCookLevin
