import PlanarHom.MachineComposition

/-! # Exact stack-bank lifting for returning Boolean-alphabet TM2 subroutines -/
namespace PlanarHom.BitMachineSubroutine

open Turing Turing.TM2
open PlanarHom.MachineComposition

variable {K J Λ Μ σ : Type}

/-- A literal right-hand bank for a Boolean-alphabet machine. -/
def bankEmbedding (J K : Type) : StackEmbedding (fun _ : K => Bool) (fun _ : J ⊕ K => Bool) where
  index := ⟨Sum.inr, Sum.inr_injective⟩
  alphabet _ := Equiv.refl Bool

/-- Lift a configuration while retaining arbitrary caller-owned words. -/
def bankCfg (outside : J → List Bool) (c : Cfg (fun _ : K => Bool) Λ σ) :
    Cfg (fun _ : J ⊕ K => Bool) (Μ ⊕ Λ) (σ × Unit) :=
  ⟨c.l.map Sum.inr, (c.var, ()), Sum.elim outside c.stk⟩

private theorem cfg_ext {K Λ σ : Type} {Γ : K → Type} (a b : Cfg Γ Λ σ)
    (hl : a.l = b.l) (hv : a.var = b.var) (hs : a.stk = b.stk) : a = b := by
  cases a
  cases b
  simp_all

/-- Exact instruction simulation, including all untouched caller stacks. -/
theorem bankStmt_correct [DecidableEq K] [DecidableEq J]
    (outside : J → List Bool) (q : Stmt (fun _ : K => Bool) Λ σ)
    (v : σ) (S : K → List Bool) :
    stepAux (liftStmt (bankEmbedding J K) (Sum.inr : Λ → Μ ⊕ Λ) q)
      (v, ()) (Sum.elim outside S) = bankCfg outside (stepAux q v S) := by
  have hr := liftStmt_correct (bankEmbedding J K) (Sum.inr : Λ → Μ ⊕ Λ) q v () S
    (Sum.elim outside S) (by intro k; simp [bankEmbedding])
  apply cfg_ext _ _ hr.1 hr.2.1
  funext k
  cases k with
  | inr k => simpa [bankCfg, bankEmbedding] using hr.2.2 k
  | inl j =>
    have h := liftStmt_untouched (bankEmbedding J K) (Sum.inr : Λ → Μ ⊕ Λ) q
      (v, ()) (Sum.elim outside S) (Sum.inl j) (by intro k; simp [bankEmbedding])
    simpa [bankCfg] using h

/-- Redirecting the source halt returns control to a fixed caller label. -/
theorem bankStmt_return_correct [DecidableEq K] [DecidableEq J]
    (outside : J → List Bool) (next : Μ) (q : Stmt (fun _ : K => Bool) Λ σ)
    (v : σ) (S : K → List Bool) :
    stepAux (redirectHalt (Sum.inl next)
      (liftStmt (bankEmbedding J K) (Sum.inr : Λ → Μ ⊕ Λ) q))
      (v, ()) (Sum.elim outside S) =
        continueCfg (Sum.inl next) (bankCfg outside (stepAux q v S)) := by
  rw [redirectHalt_correct, bankStmt_correct]

end PlanarHom.BitMachineSubroutine
