import PlanarHom.CountingCookLevinRegisterOrder

/-! The uniform arithmetic references are exactly the semantic local wiring. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic

def initialBit (m : Machine) (x : Complexity.Bits) {L : ℕ} : StateBit m L → Bool
  | .inl (.inl q) => decide (Control.run m.start=q)
  | .inl (.inr (.inl a)) => initialHeadTest m a x
  | .inl (.inr (.inr b)) => decide (true=b)
  | .inr (side,i,a) => initialCellTest m a (x,(side,i.val))

theorem initialBit_correct (m : Machine) (x : Complexity.Bits) {L : ℕ} (out : StateBit m L) :
    initialBit m x out=stateBits m (encodeWindow m L (initial m x),true) out := by
  rcases out with (q | (a | b)) | ⟨side,i,a⟩
  · rfl
  · exact initialHeadTest_correct m a x
  · rfl
  · rw [initialBit,initialCellTest_correct]
    cases side <;> rfl

def globalReference (m : Machine) (C : ℕ) (p : RefInput) :
    LayerInput m (p.1.length+p.2.1) → ℕ
  | .inr b => groundReference p b
  | .inl (.inr b) => if b then p.2.2.1 else timeStart m C p
  | .inl (.inl s) => stateReference m C p (stateOrdinal m s) (initialBit m p.1 s)

@[simp] theorem refWidth_setCell (p : RefInput) (i : ℕ) : refWidth (setCell p i)=refWidth p := rfl
@[simp] theorem timeStart_setCell (m : Machine) (C : ℕ) (p : RefInput) (i : ℕ) :
    timeStart m C (setCell p i)=timeStart m C p := rfl
@[simp] theorem groundReference_setCell (p : RefInput) (i : ℕ) (b : Bool) :
    groundReference (setCell p i) b=groundReference p b := rfl
@[simp] theorem stateReference_setCell (m : Machine) (C : ℕ) (p : RefInput) (i slot : ℕ) (b : Bool) :
    stateReference m C (setCell p i) slot b=stateReference m C p slot b := rfl
@[simp] theorem cellOrdinal_setCell (m : Machine) (p : RefInput) (i : ℕ) (side : Bool) (j : ℕ) (a : Option m.Γ) :
    cellOrdinal m (setCell p i) side j a=cellOrdinal m p side j a := rfl
@[simp] theorem cellReference_setCell (m : Machine) (C : ℕ) (p : RefInput) (i : ℕ)
    (side : Bool) (j : ℕ) (a : Option m.Γ) :
    cellReference m C side a (setCell p i) j=cellReference m C side a p j := rfl

/-- Every dynamically emitted local reference is the intended shared old-state,
choice, neighbor, or fixed-ground register. -/
theorem localReference_eq_wiring (m : Machine) (C : ℕ) (p : RefInput)
    (side : Bool) (i : Fin (p.1.length+p.2.1+1)) (v : LocalBit m ⊕ Bool) :
    localReference m C side (setCell p i.val) v=
      globalReference m C p (localWiring m side i v) := by
  cases v with
  | inr b => rfl
  | inl v =>
    cases v <;> simp only [localReference,localWiring,globalReference,initialBit,
      StateBit.control,StateBit.head,StateBit.valid,StateBit.cell,stateOrdinal_base,stateOrdinal_cell,
      groundReference_setCell,stateReference_setCell,cellReference_setCell,timeStart_setCell,
      refWidth_setCell,cellReference,cellOrdinal]
    all_goals first | rfl | skip
    · rename_i a
      by_cases hi : i.val=0
      · simp [setCell,hi]
      · simp only [setCell,hi,↓reduceIte]
        rw [dif_pos (by omega)]
        simp only [stateOrdinal_cell]
        rfl
    · rename_i a
      simp only [setCell,refWidth]
      by_cases h : i.val+1<p.1.length+p.2.1+1
      · rw [if_pos h,dif_pos h]
        simp only [stateOrdinal_cell]
      · rw [if_neg h,dif_neg h]

namespace Expr

theorem output_rename {V W : Type} (e : Expr V) (f : V → W) (start : ℕ) (ρ : W → ℕ) :
    (e.rename f).output start ρ=e.output start (ρ ∘ f) := by
  cases e <;> simp [rename,output,gates_rename]

theorem emit_rename {V W : Type} (e : Expr V) (f : V → W) (start : ℕ) (ρ : W → ℕ) :
    (e.rename f).emit start ρ=e.emit start (ρ ∘ f) := by
  induction e generalizing start with
  | var v => rfl
  | nor a b ia ib => simp [rename,emit,ia,ib,gates_rename,output_rename]

theorem copyOutput_rename {V W : Type} (e : Expr V) (f : V → W) :
    (e.rename f).copyOutput=e.copyOutput.rename f := rfl

theorem regularBlock_rename {V W : Type} (e : Expr V) (f : V → W) (C start : ℕ) (ρ : W → ℕ) :
    (e.rename f).regularBlock C start ρ=e.regularBlock C start (ρ ∘ f) := by
  simp only [regularBlock,copyOutput_rename,gates_rename,emit_rename]

end Expr

/-- Reindexing the fixed local input alphabet does not change the emitted
regular block; the concrete reference vector realizes the semantic wiring. -/
theorem numericLocalBlock_eq (m : Machine) (C : ℕ) (p : RefInput) (side : Bool)
    (i : Fin (p.1.length+p.2.1+1)) (f : LocalContext m → Bool) (start : ℕ) :
    (numericLocalTemplate m f).regularBlock C start (referenceVector m C side (setCell p i.val))=
      (wiredTemplate m side i f).regularBlock C start (globalReference m C p) := by
  simp only [numericLocalTemplate,wiredTemplate,Expr.regularBlock_rename]
  congr 1
  funext v
  simp only [Function.comp_apply,referenceVector,Equiv.symm_apply_apply]
  exact localReference_eq_wiring m C p side i v

end PlanarHom.CountingCookLevin
