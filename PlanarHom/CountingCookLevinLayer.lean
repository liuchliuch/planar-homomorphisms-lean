import PlanarHom.CountingCookLevinLocalBoolean

/-! Shared-register Boolean layer for every cell of the actual finite tape.
The wiring uses only the current cell and its immediate neighbors. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic

abbrev StateBit (m : Machine) (L : ℕ) :=
  (Control m.Q ⊕ (m.Γ ⊕ Bool)) ⊕ (Bool × Fin (L+1) × Option m.Γ)

namespace StateBit

def control (m : Machine) {L : ℕ} (q : Control m.Q) : StateBit m L := .inl (.inl q)
def head (m : Machine) {L : ℕ} (a : m.Γ) : StateBit m L := .inl (.inr (.inl a))
def valid (m : Machine) {L : ℕ} (b : Bool) : StateBit m L := .inl (.inr (.inr b))
def cell (m : Machine) {L : ℕ} (side : Bool) (i : Fin (L+1)) (a : Option m.Γ) : StateBit m L :=
  .inr (side,i,a)

end StateBit

def stateBits (m : Machine) {L : ℕ} (s : ReplayState m L) : StateBit m L → Bool
  | .inl (.inl q) => decide (s.1.1.1=q)
  | .inl (.inr (.inl a)) => decide (s.1.1.2=a)
  | .inl (.inr (.inr b)) => decide (s.2=b)
  | .inr (side,i,a) => decide ((if side then s.1.2.1 else s.1.2.2) i=a)

abbrev LayerInput (m : Machine) (L : ℕ) := (StateBit m L ⊕ Bool) ⊕ Bool

def layerInputs (m : Machine) {L : ℕ} (s : ReplayState m L) (b : Bool) : LayerInput m L → Bool :=
  Expr.grounded (Sum.elim (stateBits m s) (fun expected => decide (b=expected)))

/-- The second Bool summand consists of fixed grounded constants. -/
def localWiring (m : Machine) {L : ℕ} (side : Bool) (i : Fin (L+1)) :
    LocalBit m ⊕ Bool → LayerInput m L
  | .inr b => .inr b
  | .inl (.control q) => .inl (.inl (StateBit.control m q))
  | .inl (.head a) => .inl (.inl (StateBit.head m a))
  | .inl (.valid b) => .inl (.inl (StateBit.valid m b))
  | .inl (.choice b) => .inl (.inr b)
  | .inl (.leftHead a) => .inl (.inl (StateBit.cell m true 0 a))
  | .inl (.rightHead a) => .inl (.inl (StateBit.cell m false 0 a))
  | .inl (.current a) => .inl (.inl (StateBit.cell m side i a))
  | .inl (.previous a) => if h : 0 < i.val then
      .inl (.inl (StateBit.cell m side ⟨i.val-1,by omega⟩ a)) else .inr (decide (none=a))
  | .inl (.next a) => if h : i.val+1 < L+1 then
      .inl (.inl (StateBit.cell m side ⟨i.val+1,h⟩ a)) else .inr (decide (none=a))
  | .inl (.first b) => .inr (decide ((decide (i.val=0))=b))
  | .inl (.leftSide b) => .inr (decide (side=b))

/-- Literal wiring recovers exactly the local-context bit tests. -/
theorem localWiring_correct (m : Machine) {L : ℕ} (s : ReplayState m L)
    (b side : Bool) (i : Fin (L+1)) (v : LocalBit m ⊕ Bool) :
    layerInputs m s b (localWiring m side i v)=
      Expr.grounded (contextBits m (contextAt m s b side i)) v := by
  cases v with
  | inr v => rfl
  | inl v =>
    cases v <;> simp only [localWiring,layerInputs,Expr.grounded,Sum.elim_inl,Sum.elim_inr,
      stateBits,StateBit.control,StateBit.head,StateBit.valid,StateBit.cell,contextBits,contextAt,
      previousCell,nextCell,id_eq]
    all_goals first | rfl | (split <;> rfl)

/-- Each output is a fixed template with purely local register renaming. -/
def wiredTemplate (m : Machine) {L : ℕ} (side : Bool) (i : Fin (L+1))
    (f : LocalContext m → Bool) : Expr (LayerInput m L) :=
  (localTemplate m f).rename (localWiring m side i)

theorem wiredTemplate_correct (m : Machine) {L : ℕ} (s : ReplayState m L)
    (b side : Bool) (i : Fin (L+1)) (f : LocalContext m → Bool) :
    (wiredTemplate m side i f).eval (layerInputs m s b)=f (contextAt m s b side i) := by
  rw [wiredTemplate,Expr.eval_rename]
  have h := (localTemplate m f).eval_congr
    (layerInputs m s b ∘ localWiring m side i)
    (Expr.grounded (contextBits m (contextAt m s b side i)))
    (fun v => localWiring_correct m s b side i v)
  exact h.trans (localTemplate_correct m f _)

/-- The full next-state circuit layer; old-state wires remain shared inputs. -/
def stepLayer (m : Machine) {L : ℕ} : StateBit m L → Expr (LayerInput m L)
  | .inl (.inl q) => wiredTemplate m false 0 (fun c => decide (localControl m c=q))
  | .inl (.inr (.inl a)) => wiredTemplate m false 0 (fun c => decide (localHead m c=a))
  | .inl (.inr (.inr v)) => wiredTemplate m false 0 (fun c => decide (localValid m c=v))
  | .inr (side,i,a) => wiredTemplate m side i (fun c => decide (localCell m c=a))

/-- This is the actual machine step, bit for bit, rather than an assumed
local expressibility condition. -/
theorem stepLayer_correct (m : Machine) {L : ℕ} (s : ReplayState m L) (b : Bool)
    (out : StateBit m L) :
    (stepLayer m out).eval (layerInputs m s b)=stateBits m (windowStep m s b) out := by
  rcases out with (q | (a | v)) | ⟨side,i,a⟩
  · simp only [stepLayer,wiredTemplate_correct,stateBits]
    rw [(windowStep_local_controls m s b false 0).1]
  · simp only [stepLayer,wiredTemplate_correct,stateBits]
    rw [(windowStep_local_controls m s b false 0).2.1]
  · simp only [stepLayer,wiredTemplate_correct,stateBits]
    rw [(windowStep_local_controls m s b false 0).2.2]
  · simp only [stepLayer,wiredTemplate_correct,stateBits]
    rw [windowStep_local_cell]

/-- The number of Boolean state registers is linear in tape-window width;
all coefficients are cardinalities of fixed source-machine alphabets. -/
theorem stateBit_card (m : Machine) (L : ℕ) :
    Fintype.card (StateBit m L)=Fintype.card (Control m.Q)+Fintype.card m.Γ+2+
      2*(L+1)*(Fintype.card m.Γ+1) := by
  simp only [StateBit,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,
    Fintype.card_fin,Fintype.card_option]
  ring

open scoped BigOperators

/-- A single source-machine constant pays for every possible local template. -/
def localGateBound (m : Machine) : ℕ :=
  (∑ q : Control m.Q, (localTemplate m (fun c => decide (localControl m c=q))).gates) +
  (∑ a : m.Γ, (localTemplate m (fun c => decide (localHead m c=a))).gates) +
  (∑ b : Bool, (localTemplate m (fun c => decide (localValid m c=b))).gates) +
  (∑ a : Option m.Γ, (localTemplate m (fun c => decide (localCell m c=a))).gates)

theorem stepLayer_gates_le (m : Machine) {L : ℕ} (out : StateBit m L) :
    (stepLayer m out).gates≤localGateBound m := by
  rcases out with (q | (a | v)) | ⟨side,i,a⟩
  · have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun q : Control m.Q => (localTemplate m (fun c => decide (localControl m c=q))).gates)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    dsimp only at h
    simp only [stepLayer,wiredTemplate,Expr.gates_rename,localGateBound]
    omega
  · have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun a : m.Γ => (localTemplate m (fun c => decide (localHead m c=a))).gates)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    dsimp only at h
    simp only [stepLayer,wiredTemplate,Expr.gates_rename,localGateBound]
    omega
  · have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun v : Bool => (localTemplate m (fun c => decide (localValid m c=v))).gates)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    dsimp only at h
    simp only [stepLayer,wiredTemplate,Expr.gates_rename,localGateBound]
    omega
  · have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun a : Option m.Γ => (localTemplate m (fun c => decide (localCell m c=a))).gates)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    dsimp only at h
    simp only [stepLayer,wiredTemplate,Expr.gates_rename,localGateBound]
    omega

/-- Actual total local-template gate count is linear in width. It does not
enumerate global states, and its constant is independent of the clock. -/
theorem stepLayer_total_gates (m : Machine) (L : ℕ) :
    (∑ out : StateBit m L, (stepLayer m out).gates) ≤
      (Fintype.card (Control m.Q)+Fintype.card m.Γ+2+2*(L+1)*(Fintype.card m.Γ+1))*localGateBound m := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (StateBit m L))) (fun out _ => stepLayer_gates_le m out)
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,stateBit_card] using h

end PlanarHom.CountingCookLevin
