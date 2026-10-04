import PlanarHom.CountingCookLevinLayer

/-! An explicit uniform arithmetic layout for the circuit's Boolean registers.
Only fixed source-machine alphabets use fixed finite enumeration. -/
noncomputable section
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic

abbrev BaseStateBit (m : Machine) := Control m.Q ⊕ (m.Γ ⊕ Bool)

def stateRegisterCount (m : Machine) (L : ℕ) : ℕ :=
  Fintype.card (BaseStateBit m)+2*((L+1)*Fintype.card (Option m.Γ))

def stateIndexEquiv (m : Machine) (L : ℕ) : StateBit m L ≃ Fin (stateRegisterCount m L) :=
  (Equiv.sumCongr (Fintype.equivFin (BaseStateBit m))
    ((Equiv.prodCongr (Fintype.equivFin Bool)
      ((Equiv.prodCongr (Equiv.refl (Fin (L+1))) (Fintype.equivFin (Option m.Γ))).trans
        finProdFinEquiv)).trans finProdFinEquiv)).trans finSumFinEquiv

def stateOrdinal (m : Machine) {L : ℕ} (s : StateBit m L) : ℕ := (stateIndexEquiv m L s).val

@[simp] theorem stateOrdinal_base (m : Machine) {L : ℕ} (b : BaseStateBit m) :
    stateOrdinal m (L := L) (.inl b)=(Fintype.equivFin (BaseStateBit m) b).val := rfl

@[simp] theorem stateOrdinal_cell (m : Machine) {L : ℕ} (side : Bool) (i : Fin (L+1)) (a : Option m.Γ) :
    stateOrdinal m (.inr (side,i,a)) = Fintype.card (BaseStateBit m)+
      ((L+1)*Fintype.card (Option m.Γ))*(Fintype.equivFin Bool side).val+
      (Fintype.card (Option m.Γ))*i.val+(Fintype.equivFin (Option m.Γ) a).val := by
  change Fintype.card (BaseStateBit m) +
    ((Fintype.equivFin (Option m.Γ) a).val+Fintype.card (Option m.Γ)*i.val+
      ((L+1)*Fintype.card (Option m.Γ))*(Fintype.equivFin Bool side).val)=_
  omega

def stateRegisterOrder (m : Machine) (L : ℕ) : List (StateBit m L) :=
  List.ofFn (stateIndexEquiv m L).symm

@[simp] theorem stateRegisterOrder_length (m : Machine) (L : ℕ) :
    (stateRegisterOrder m L).length=stateRegisterCount m L := by simp [stateRegisterOrder]

theorem stateRegisterOrder_nodup (m : Machine) (L : ℕ) : (stateRegisterOrder m L).Nodup :=
  List.nodup_ofFn.mpr (stateIndexEquiv m L).symm.injective

theorem stateRegisterOrder_get (m : Machine) {L : ℕ} (s : StateBit m L) :
    (stateRegisterOrder m L)[stateOrdinal m s]?=some s := by
  simp [stateRegisterOrder,stateOrdinal]

/-- All source-machine state registers occur in this explicit arithmetic layout. -/
theorem stateRegisterOrder_complete (m : Machine) {L : ℕ} (s : StateBit m L) :
    s∈stateRegisterOrder m L := List.mem_of_getElem? (stateRegisterOrder_get m s)

end PlanarHom.CountingCookLevin
