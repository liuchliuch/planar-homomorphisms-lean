import PlanarHom.MachineComposition

/-! # Costed refinement of mathlib's TM1-to-TM0 compiler

Mathlib's existing translation exposes each tape movement or write as an actual
TM0 transition. This file proves an exact finite transition count and a fixed
syntax bound for one macro statement. It is not a complete multistack-to-tape
polynomial compiler or a counting-class equivalence.
-/
namespace PlanarHom.TM1PrimitiveTimeBounds
open Turing

variable {Γ Λ σ : Type} [Inhabited Γ]

/-- Count the primitive transitions actually selected by finite control. -/
def steps : TM1.Stmt Γ Λ σ → σ → Tape Γ → ℕ
  | .move d q,v,t => 1+steps q v (t.move d)
  | .write f q,v,t => 1+steps q v (t.write (f t.head v))
  | .load f q,v,t => steps q (f t.head v) t
  | .branch f q r,v,t => if f t.head v then steps q v t else steps r v t
  | .goto _,_,_ => 1
  | .halt,_,_ => 1

/-- A finite program constant; both branches are counted conservatively. -/
def bound : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => 1+bound q
  | .write _ q => 1+bound q
  | .load _ q => bound q
  | .branch _ q r => bound q+bound r
  | .goto _ => 1
  | .halt => 1

theorem steps_pos (q : TM1.Stmt Γ Λ σ) (v : σ) (t : Tape Γ) : 0 < steps q v t := by
  induction q generalizing v t with
  | move d q ih => simp [steps]
  | write f q ih => simp [steps]
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr => cases h : f t.head v <;> simp [steps,h,ihq,ihr]
  | goto f => exact Nat.zero_lt_one
  | halt => exact Nat.zero_lt_one

theorem steps_le (q : TM1.Stmt Γ Λ σ) (v : σ) (t : Tape Γ) : steps q v t ≤ bound q := by
  induction q generalizing v t with
  | move d q ih => simpa [steps,bound] using Nat.add_le_add_left (ih v (t.move d)) 1
  | write f q ih => simpa [steps,bound] using Nat.add_le_add_left (ih v (t.write (f t.head v))) 1
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
    cases h : f t.head v
    · simp only [steps,bound,h,Bool.false_eq_true,if_false]
      exact (ihr v t).trans (Nat.le_add_left _ _)
    · simp only [steps,bound,h,if_true]
      exact (ihq v t).trans (Nat.le_add_right _ _)
  | goto f => exact Nat.le_refl _
  | halt => exact Nat.le_refl _

section Compilation
variable [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ)

abbrev TargetCfg := TM0.Cfg Γ (TM1to0.Λ' M)

def iter (n : ℕ) (c : TargetCfg M) : Option (TargetCfg M) :=
  (fun c : Option (TargetCfg M) => c.bind (TM0.step (TM1to0.tr M)))^[n] (some c)

/-- Equal first primitive transitions give equal positive-length iterations. -/
theorem iter_eq_of_step_eq {c d : TargetCfg M} (n : ℕ) (hn : 0<n)
    (h : TM0.step (TM1to0.tr M) c = TM0.step (TM1to0.tr M) d) :
    iter M n c=iter M n d := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  simp only [iter,Function.iterate_succ_apply,Option.bind_some,h]

/-- The existing syntax compiler performs exactly `steps` real TM0 transitions
and ends at the exact translated configuration, including its whole tape. -/
theorem compile_exact (q : TM1.Stmt Γ Λ σ) (v : σ) (t : Tape Γ) :
    iter M (steps q v t) ⟨(some q,v),t⟩ =
      some (TM1to0.trCfg M (TM1.stepAux q v t)) := by
  induction q generalizing v t with
  | move d q ih =>
    rw [steps,Nat.add_comm,iter,Function.iterate_succ_apply]
    change (fun c : Option (TargetCfg M) => c.bind (TM0.step (TM1to0.tr M)))^[steps q v (t.move d)]
      (some ⟨(some q,v),t.move d⟩) = _
    exact ih v (t.move d)
  | write f q ih =>
    rw [steps,Nat.add_comm,iter,Function.iterate_succ_apply]
    change (fun c : Option (TargetCfg M) => c.bind (TM0.step (TM1to0.tr M)))^[steps q v (t.write (f t.head v))]
      (some ⟨(some q,v),t.write (f t.head v)⟩) = _
    exact ih v (t.write (f t.head v))
  | load f q ih =>
    change iter M (steps q (f t.head v) t) ⟨(some (.load f q),v),t⟩ = _
    rw [iter_eq_of_step_eq M _ (steps_pos q (f t.head v) t)
      (show TM0.step (TM1to0.tr M) ⟨(some (.load f q),v),t⟩ =
        TM0.step (TM1to0.tr M) ⟨(some q,f t.head v),t⟩ from rfl)]
    exact ih _ _
  | branch f q r ihq ihr =>
    cases h : f t.head v with
    | false =>
      simp only [steps,h,Bool.false_eq_true,if_false]
      rw [iter_eq_of_step_eq M _ (steps_pos r v t)
        (show TM0.step (TM1to0.tr M) ⟨(some (.branch f q r),v),t⟩ =
          TM0.step (TM1to0.tr M) ⟨(some r,v),t⟩ by simp [TM0.step,TM1to0.tr,TM1to0.trAux,h])]
      simpa [TM1.stepAux,h] using ihr v t
    | true =>
      simp only [steps,h,if_true]
      rw [iter_eq_of_step_eq M _ (steps_pos q v t)
        (show TM0.step (TM1to0.tr M) ⟨(some (.branch f q r),v),t⟩ =
          TM0.step (TM1to0.tr M) ⟨(some q,v),t⟩ by simp [TM0.step,TM1to0.tr,TM1to0.trAux,h])]
      simpa [TM1.stepAux,h] using ihq v t
  | goto f => simp [iter,steps,TM0.step,TM1to0.tr,TM1to0.trAux,TM1to0.trCfg,TM1.stepAux,Tape.write_self]
  | halt => simp [iter,steps,TM0.step,TM1to0.tr,TM1to0.trAux,TM1to0.trCfg,TM1.stepAux,Tape.write_self]

end Compilation
end PlanarHom.TM1PrimitiveTimeBounds
