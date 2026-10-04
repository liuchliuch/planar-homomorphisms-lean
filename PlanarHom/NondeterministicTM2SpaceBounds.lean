import PlanarHom.NondeterministicTM2
import PlanarHom.MachineComposition
import PlanarHom.TM2TapeStatementBounds
import Mathlib.Tactic.Linarith

/-! # Materialized stack bounds for every nondeterministic branch

Source control and syntax determine these constants. The potential includes all
remaining source steps, so it decreases across both ordinary and binary edges.
-/
namespace PlanarHom.NondeterministicTM2SpaceBounds
noncomputable section
open Turing NondeterministicTM2 NondeterministicComputationTree
open MachineComposition TM2TapeStatementBounds

def pushConstant (m : Machine) : ℕ := machinePushBound m.core.tm

def operationConstant (m : Machine) : ℕ :=
  @Finset.sum m.core.tm.Λ ℕ _ (@Finset.univ _ m.core.tm.ΛFin)
    (fun l => stackOps (m.core.tm.m l))

theorem push_le (m : Machine) (l : m.core.tm.Λ) :
    pushBound (m.core.tm.m l) ≤ pushConstant m := by
  letI := m.core.tm.ΛFin
  exact Finset.single_le_sum (f := fun l => pushBound (m.core.tm.m l))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

theorem operations_le (m : Machine) (l : m.core.tm.Λ) :
    stackOps (m.core.tm.m l) ≤ operationConstant m := by
  letI := m.core.tm.ΛFin
  exact Finset.single_le_sum (f := fun l => stackOps (m.core.tm.m l))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

theorem initial_length (m : Machine) (x : Complexity.Bits) :
    ∀k,((m.initial x).stk k).length ≤ x.length := by
  intro k
  by_cases hk : k=m.core.tm.k₀
  · subst k; simp [Machine.initial,initList]
  · simp [Machine.initial,initList,hk]

/-- Inverting a source ordinary node exposes its literal TM2 instruction. -/
theorem ordinary_inv (m : Machine) {c next : m.Cfg} (h : m.view c=.ordinary next) :
    ∃ l, c.l=some l ∧ m.branch l=none ∧ next=TM2.stepAux (m.core.tm.m l) c.var c.stk := by
  cases hl : c.l with
  | none => simp only [Machine.view,hl] at h; split at h <;> cases h
  | some l =>
    cases hb : m.branch l with
    | none => exact ⟨l,rfl,hb,by simpa only [Machine.view,hl,hb,NodeView.ordinary.injEq] using h.symm⟩
    | some p => simp only [Machine.view,hl,hb] at h; cases h

theorem binary_inv (m : Machine) {c left right : m.Cfg} (h : m.view c=.binary left right) :
    ∃ l a b, c.l=some l ∧ m.branch l=some (a,b) ∧ left=m.jump c a ∧ right=m.jump c b := by
  cases hl : c.l with
  | none => simp only [Machine.view,hl] at h; split at h <;> cases h
  | some l =>
    cases hb : m.branch l with
    | none => simp only [Machine.view,hl,hb] at h; cases h
    | some p =>
      obtain ⟨a,b⟩ := p
      have he : m.jump c a=left ∧ m.jump c b=right := by
        simpa only [Machine.view,hl,hb,NodeView.binary.injEq] using h
      exact ⟨l,a,b,rfl,hb,he.1.symm,he.2.symm⟩

theorem accept_inv (m : Machine) {c : m.Cfg} (h : m.view c=.accept) :
    c.l=none ∧ m.output c=[true] := by
  cases hl : c.l with
  | none =>
    refine ⟨rfl,?_⟩
    by_cases he : m.output c=[true]
    · exact he
    · simp [Machine.view,hl,he] at h
  | some l => cases hb : m.branch l <;> simp [Machine.view,hl,hb] at h

theorem reject_inv (m : Machine) {c : m.Cfg} (h : m.view c=.reject) :
    c.l=none ∧ m.output c≠[true] := by
  cases hl : c.l with
  | none =>
    refine ⟨rfl,?_⟩
    intro he
    simp [Machine.view,hl,he] at h
  | some l => cases hb : m.branch l <;> simp [Machine.view,hl,hb] at h

/-- Uniform materialized space, including the maximum growth of every remaining
source transition. This is a proof invariant, not data stored by the target. -/
def Space (m : Machine) (cap fuel : ℕ) (c : m.Cfg) : Prop :=
  ∃ size, (∀k,(c.stk k).length ≤ size) ∧ size+fuel*pushConstant m ≤ cap

theorem initial_space (m : Machine) (x : Complexity.Bits) (fuel : ℕ) :
    Space m (x.length+fuel*pushConstant m) fuel (m.initial x) :=
  ⟨x.length,initial_length m x,le_rfl⟩

theorem ordinary_space (m : Machine) {cap fuel : ℕ} {c next : m.Cfg}
    (hs : Space m cap (fuel+1) c) (h : m.view c=.ordinary next) : Space m cap fuel next := by
  obtain ⟨size,hsize,hcap⟩ := hs
  obtain ⟨l,hl,hb,rfl⟩ := ordinary_inv m h
  refine ⟨size+pushConstant m,?_,?_⟩
  · intro k
    exact (stepAux_length_le (m.core.tm.m l) c.var c.stk size hsize k).trans
      (Nat.add_le_add_left (push_le m l) size)
  · nlinarith

theorem jump_space (m : Machine) {cap fuel : ℕ} {c : m.Cfg}
    (hs : Space m cap (fuel+1) c) (l : m.core.tm.Λ) : Space m cap fuel (m.jump c l) := by
  obtain ⟨size,hsize,hcap⟩ := hs
  exact ⟨size,hsize,by nlinarith⟩

end
end PlanarHom.NondeterministicTM2SpaceBounds
