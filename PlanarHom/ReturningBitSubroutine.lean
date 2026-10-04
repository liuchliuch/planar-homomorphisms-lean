import PlanarHom.BitMachineSubroutine

/-! # General returning subroutine compilation with a finite-control equivalence -/
namespace PlanarHom.ReturningBitSubroutine
open Turing Turing.TM2
open PlanarHom.MachineComposition

variable {K J Λ Μ σ τ : Type}

def dropUnit (σ : Type) : σ × Unit ≃ σ where
  toFun := Prod.fst
  invFun v := (v, ())
  left_inv v := by rcases v with ⟨v,u⟩; cases u; rfl
  right_inv _ := rfl

def stackEmbedding (e : K ↪ J) : StackEmbedding (fun _ : K => Bool) (fun _ : J => Bool) where
  index := e
  alphabet _ := Equiv.refl Bool

/-- Compile only syntax and finite control; halt becomes a caller continuation. -/
def compile (e : K ↪ J) (labels : Λ → Μ) (state : σ ≃ τ) (next : Μ)
    (q : Stmt (fun _ : K => Bool) Λ σ) : Stmt (fun _ : J => Bool) Μ τ :=
  redirectHalt next (renameState ((dropUnit σ).trans state)
    (liftStmt (stackEmbedding e) labels q))

/-- Full source simulation, fixing every stack outside the source bank. -/
def Rel (e : K ↪ J) (labels : Λ → Μ) (state : σ ≃ τ) (next : Μ)
    (outside : J → List Bool) (a : Cfg (fun _ : K => Bool) Λ σ)
    (b : Cfg (fun _ : J => Bool) Μ τ) : Prop :=
  b.l = (a.l.map labels).or (some next) ∧ b.var = state a.var ∧
    (∀ k, b.stk (e k) = a.stk k) ∧
    (∀ j, (∀ k, j ≠ e k) → b.stk j = outside j)

theorem rel_unique (e : K ↪ J) (labels : Λ → Μ) (state : σ ≃ τ) (next : Μ)
    (outside : J → List Bool) (a : Cfg (fun _ : K => Bool) Λ σ)
    (b c : Cfg (fun _ : J => Bool) Μ τ)
    (hb : Rel e labels state next outside a b) (hc : Rel e labels state next outside a c) : b = c := by
  have hl : b.l = c.l := hb.1.trans hc.1.symm
  have hv : b.var = c.var := hb.2.1.trans hc.2.1.symm
  have hs : b.stk = c.stk := by
    funext j
    by_cases hj : ∃ k, e k = j
    · obtain ⟨k,rfl⟩ := hj
      exact (hb.2.2.1 k).trans (hc.2.2.1 k).symm
    · have hj' : ∀ k, j ≠ e k := by intro k hk; exact hj ⟨k,hk.symm⟩
      exact (hb.2.2.2 j hj').trans (hc.2.2.2 j hj').symm
  cases b
  cases c
  simp_all

theorem compile_correct [DecidableEq K] [DecidableEq J]
    (e : K ↪ J) (labels : Λ → Μ) (state : σ ≃ τ) (next : Μ)
    (outside : J → List Bool) (q : Stmt (fun _ : K => Bool) Λ σ)
    (v : σ) (S : K → List Bool) (T : J → List Bool)
    (hb : ∀ k, T (e k) = S k)
    (ho : ∀ j, (∀ k, j ≠ e k) → T j = outside j) :
    Rel e labels state next outside (stepAux q v S) (stepAux (compile e labels state next q) (state v) T) := by
  have h := liftStmt_correct (stackEmbedding e) labels q v () S T (by
    intro k; simpa [stackEmbedding] using hb k)
  have he : stepAux (compile e labels state next q) (state v) T =
      continueCfg next (renameCfgState ((dropUnit σ).trans state)
        (stepAux (liftStmt (stackEmbedding e) labels q) (v, ()) T)) := by
    unfold compile
    rw [redirectHalt_correct]
    exact congrArg (continueCfg next)
      (renameState_correct ((dropUnit σ).trans state) _ (v, ()) T)
  rw [he]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [continueCfg, renameCfgState] using congrArg (fun l => l.or (some next)) h.1
  · simpa [continueCfg, renameCfgState, dropUnit] using congrArg (fun w => state w.1) h.2.1
  · intro k
    simpa [continueCfg, renameCfgState, stackEmbedding] using h.2.2 k
  · intro j hj
    have hu := liftStmt_untouched (stackEmbedding e) labels q (v, ()) T j hj
    simpa [continueCfg, renameCfgState] using hu.trans (ho j hj)

theorem simulate_step [DecidableEq K] [DecidableEq J]
    (e : K ↪ J) (labels : Λ → Μ) (state : σ ≃ τ) (next : Μ)
    (outside : J → List Bool) (source : Λ → Stmt (fun _ : K => Bool) Λ σ)
    (target : Μ → Stmt (fun _ : J => Bool) Μ τ)
    (hm : ∀ l, target (labels l) = compile e labels state next (source l))
    (a a' : Cfg (fun _ : K => Bool) Λ σ) (b : Cfg (fun _ : J => Bool) Μ τ)
    (hs : step source a = some a') (hr : Rel e labels state next outside a b) :
    ∃ b', step target b = some b' ∧ Rel e labels state next outside a' b' := by
  rcases a with ⟨l,v,S⟩
  cases l with
  | none => simp [step] at hs
  | some l =>
    simp only [step, Option.some.injEq] at hs
    subst a'
    have hl : b.l = some (labels l) := by simpa using hr.1
    have hv : b.var = state v := hr.2.1
    refine ⟨stepAux (compile e labels state next (source l)) (state v) b.stk, ?_, ?_⟩
    · cases b
      simp_all [step]
    · exact compile_correct e labels state next outside (source l) v S _ hr.2.2.1 hr.2.2.2

/-- Transfer an exact bounded execution into its caller bank with no overhead. -/
def run [DecidableEq K] [DecidableEq J]
    (e : K ↪ J) (labels : Λ → Μ) (state : σ ≃ τ) (next : Μ)
    (outside : J → List Bool) (source : Λ → Stmt (fun _ : K => Bool) Λ σ)
    (target : Μ → Stmt (fun _ : J => Bool) Μ τ)
    (hm : ∀ l, target (labels l) = compile e labels state next (source l))
    (a a' : Cfg (fun _ : K => Bool) Λ σ) (b b' : Cfg (fun _ : J => Bool) Μ τ) (n : ℕ)
    (h : EvalsToInTime (step source) a (some a') n)
    (hb : Rel e labels state next outside a b) (hb' : Rel e labels state next outside a' b') :
    EvalsToInTime (step target) b (some b') n := by
  refine ⟨⟨h.steps, ?_⟩, h.steps_le_m⟩
  obtain ⟨c,hc,hr⟩ := simulate_iterations (step source) (step target)
    (Rel e labels state next outside) (simulate_step e labels state next outside source target hm)
    a a' b h.steps h.evals_in_steps hb
  have he := rel_unique e labels state next outside a' c b' hr hb'
  simpa [he] using hc

end PlanarHom.ReturningBitSubroutine
