import PlanarHom.PlanarityDepthFirstSearchProgram

/-! NEW reconstruction. The explicit DFS task stack empties within the actual
polynomial fuel, on every raw graph. Discoveries remain distinct and valid. -/
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity

def potential (g : MixedCode) (s : State) : ℕ :=
  (g.vertices-s.discovered.length)*(2*g.edges.length+2)+s.work.length

 theorem step_completed (g : MixedCode) (s : State) (h : s.work=[]) : step g s=s := by
  simp [step,h]

 theorem potential_decreases (g : MixedCode) (s : State) (hseen : GoodSeen g s) (hw : s.work≠[]) :
    potential g (step g s) < potential g s := by
  have hlen := goodSeen_length g s hseen
  cases hwork : s.work with
  | nil => exact (hw hwork).elim
  | cons t rest =>
    unfold step
    rw [hwork]
    dsimp only
    split_ifs with hent hnew
    · have hnext := goodSeen_length g (step g s) (goodSeen_step g s hseen)
      simp [step,hwork,hent,hnew] at hnext
      have hs : g.vertices-s.discovered.length = g.vertices-(s.discovered.length+1)+1 := by omega
      have hn := neighbours_length g t.vertex
      simp only [potential,List.length_append,childTasks_length,List.length_cons,hwork]
      rw [hs]
      nlinarith
    · simp [potential,hwork]
    · simp [potential,hwork]

 theorem iterate_goodSeen (g : MixedCode) (n : ℕ) : GoodSeen g ((step g)^[n] (initial g)) := by
  induction n with
  | zero => exact goodSeen_initial g
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact goodSeen_step g _ ih

 theorem iterate_empties (g : MixedCode) (s : State) (hseen : GoodSeen g s)
    (n : ℕ) (hn : potential g s ≤ n) : ((step g)^[n] s).work = [] := by
  induction n generalizing s with
  | zero =>
    have hh : s.work.length=0 := by unfold potential at hn; omega
    exact List.length_eq_zero_iff.mp hh
  | succ n ih =>
    by_cases hw : s.work=[]
    · rw [Function.iterate_fixed (step_completed g s hw)]
      exact hw
    · rw [Function.iterate_succ_apply]
      exact ih (step g s) (goodSeen_step g s hseen)
        (by have hh:=potential_decreases g s hseen hw; omega)

 theorem initial_potential (g : MixedCode) : potential g (initial g) ≤ fuel g := by
  simp [potential,initial,fuel]
  nlinarith

 theorem run_complete (g : MixedCode) : (run g).work=[] :=
  iterate_empties g (initial g) (goodSeen_initial g) (fuel g) (initial_potential g)

 theorem run_goodSeen (g : MixedCode) : GoodSeen g (run g) := iterate_goodSeen g (fuel g)

 theorem run_stable (g : MixedCode) (extra : ℕ) :
    (step g)^[fuel g+extra] (initial g)=run g := by
  rw [Nat.add_comm,Function.iterate_add_apply]
  exact Function.iterate_fixed (step_completed g (run g) (run_complete g)) extra

end PlanarHom.PlanarityDepthFirstSearch
