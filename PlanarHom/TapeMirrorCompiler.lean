import PlanarHom.MachineComposition

/-! # Exact-time reversal of tape orientation by a syntax compiler

A mirrored simulation can store each input symbol in place and put the common
stack-bottom marker at the right endpoint. This compiler changes movement
instructions, rather than executing a free whole-tape reversal.
-/
namespace PlanarHom.TapeMirrorCompiler
open Turing

variable {Γ Λ σ : Type} [Inhabited Γ]

def mirror (t : Tape Γ) : Tape Γ := ⟨t.head,t.right,t.left⟩

def direction : Dir → Dir | .left => .right | .right => .left

@[simp] theorem mirror_mirror (t : Tape Γ) : mirror (mirror t)=t := by cases t; rfl
@[simp] theorem mirror_write (t : Tape Γ) (a : Γ) : mirror (t.write a)=(mirror t).write a := rfl
@[simp] theorem mirror_move (t : Tape Γ) (d : Dir) :
    mirror (t.move d)=(mirror t).move (direction d) := by cases d <;> rfl
@[simp] theorem mirror_head (t : Tape Γ) : (mirror t).head=t.head := rfl

def stmt : TM1.Stmt Γ Λ σ → TM1.Stmt Γ Λ σ
  | .move d q => .move (direction d) (stmt q)
  | .write f q => .write f (stmt q)
  | .load f q => .load f (stmt q)
  | .branch f q r => .branch f (stmt q) (stmt r)
  | .goto f => .goto f
  | .halt => .halt

def cfg (c : TM1.Cfg Γ Λ σ) : TM1.Cfg Γ Λ σ := ⟨c.l,c.var,mirror c.Tape⟩

theorem stmt_correct (q : TM1.Stmt Γ Λ σ) (v : σ) (t : Tape Γ) :
    TM1.stepAux (stmt q) v (mirror t)=cfg (TM1.stepAux q v t) := by
  induction q generalizing v t with
  | move d q ih => simpa only [stmt,TM1.stepAux,mirror_move] using ih v (t.move d)
  | write f q ih => simpa only [stmt,TM1.stepAux,mirror_write,mirror_head] using ih v (t.write (f t.head v))
  | load f q ih => simpa only [stmt,TM1.stepAux,mirror_head] using ih (f t.head v) t
  | branch f q r ihq ihr =>
    cases h : f t.head v <;> simp only [stmt,TM1.stepAux,mirror_head,h,Bool.cond_true,Bool.cond_false]
    · exact ihr _ _
    · exact ihq _ _
  | goto f => rfl
  | halt => rfl

/-- Reversing every local movement preserves exactly one machine transition. -/
theorem step_correct (M : Λ → TM1.Stmt Γ Λ σ) (c : TM1.Cfg Γ Λ σ) :
    TM1.step (fun l => stmt (M l)) (cfg c) = (TM1.step M c).map cfg := by
  rcases c with ⟨l,v,t⟩
  cases l with
  | none => rfl
  | some l => exact congrArg some (stmt_correct (M l) v t)

/-- Every exact finite execution is mirrored with exactly the same step count. -/
theorem iterate_correct (M : Λ → TM1.Stmt Γ Λ σ) (n : ℕ) (c : Option (TM1.Cfg Γ Λ σ)) :
    (fun c : Option (TM1.Cfg Γ Λ σ) => c.bind (TM1.step (fun l => stmt (M l))))^[n]
      (c.map cfg) =
      ((fun c : Option (TM1.Cfg Γ Λ σ) => c.bind (TM1.step M))^[n] c).map cfg := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
    have hs : (c.map cfg).bind (TM1.step (fun l => stmt (M l))) = (c.bind (TM1.step M)).map cfg := by
      cases c with
      | none => rfl
      | some c => exact step_correct M c
    rw [hs]
    exact ih _

end PlanarHom.TapeMirrorCompiler
