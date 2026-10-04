import PlanarHom.OccurrenceMatchingPorts
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! NEW literal alternating occurrence walk, with invertible state transitions. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph.PerfectMatching
open Kasteleyn
variable {V E : Type*} {G : MultiGraph V E} {M N : Finset E}
variable (hM : G.PerfectMatching M) (hN : G.PerfectMatching N)

def stepPerm : Equiv.Perm (V×Bool) where
  toFun s := if s.2 then (hM.mate s.1,false) else (hN.mate s.1,true)
  invFun s := if s.2 then (hN.mate s.1,false) else (hM.mate s.1,true)
  left_inv s := by rcases s with ⟨v,b⟩; cases b <;> simp [hM.mate_mate,hN.mate_mate]
  right_inv s := by rcases s with ⟨v,b⟩; cases b <;> simp [hM.mate_mate,hN.mate_mate]

def stepPort (s : V×Bool) : Dart E := if s.2 then hM.port s.1 else hN.port s.1

theorem step_color (s : V×Bool) : (hM.stepPerm hN s).2= !s.2 := by
  rcases s with ⟨v,b⟩
  cases b <;> rfl

theorem stepPort_host (s : V×Bool) : (G.dartPair (hM.stepPort hN s)).1=s.1 := by
  rcases s with ⟨v,b⟩
  cases b
  · exact hN.port_host v
  · exact hM.port_host v

theorem stepPort_head (s : V×Bool) : (G.dartPair (hM.stepPort hN s)).2=(hM.stepPerm hN s).1 := by
  rcases s with ⟨v,b⟩
  cases b <;> rfl

theorem step_vertex_ne (s : V×Bool) : (hM.stepPerm hN s).1≠s.1 := by
  rcases s with ⟨v,b⟩
  cases b
  · exact hN.mate_ne v
  · exact hM.mate_ne v

theorem differ_step (s : V×Bool) (hd : hM.Differ hN s.1) : hM.Differ hN (hM.stepPerm hN s).1 := by
  rcases s with ⟨v,b⟩
  cases b
  · exact hM.differ_mate_right hN v hd
  · exact hM.differ_mate_left hN v hd

theorem stepPort_backtrack (s t : V×Bool) (hc : s.2=t.2) (hv : (hM.stepPerm hN t).1=s.1) :
    hM.stepPort hN s=((hM.stepPort hN t).1,!(hM.stepPort hN t).2) := by
  rcases s with ⟨v,b⟩
  rcases t with ⟨w,d⟩
  dsimp at hc
  subst d
  cases b
  · change hN.mate w=v at hv
    change hN.port v=((hN.port w).1,!(hN.port w).2)
    rw [←hv,hN.port_mate]
  · change hM.mate w=v at hv
    change hM.port v=((hM.port w).1,!(hM.port w).2)
    rw [←hv,hM.port_mate]

def walkState (v : V) (n : ℕ) : V×Bool := (hM.stepPerm hN)^[n] (v,true)
def walkVertex (v : V) (n : ℕ) : V := (hM.walkState hN v n).1
def walkDart (v : V) (n : ℕ) : Dart E := hM.stepPort hN (hM.walkState hN v n)

@[simp] theorem walkState_zero (v : V) : hM.walkState hN v 0=(v,true) := rfl
@[simp] theorem walkState_succ (v : V) (n : ℕ) : hM.walkState hN v (n+1)=hM.stepPerm hN (hM.walkState hN v n) :=
  Function.iterate_succ_apply' _ _ _

theorem walkDart_host (v : V) (n : ℕ) : (G.dartPair (hM.walkDart hN v n)).1=hM.walkVertex hN v n :=
  hM.stepPort_host hN _

theorem walkDart_head (v : V) (n : ℕ) : (G.dartPair (hM.walkDart hN v n)).2=hM.walkVertex hN v (n+1) := by
  simpa only [walkVertex,walkState_succ] using hM.stepPort_head hN (hM.walkState hN v n)

theorem walkVertex_succ_ne (v : V) (n : ℕ) : hM.walkVertex hN v (n+1)≠hM.walkVertex hN v n :=
by
  simpa only [walkVertex,walkState_succ] using hM.step_vertex_ne hN (hM.walkState hN v n)

theorem walkState_color (v : V) (n : ℕ) : (hM.walkState hN v n).2=decide (n%2=0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [walkState_succ,hM.step_color,ih]
      by_cases hn:n%2=0
      · have hs:(n+1)%2=1:=by omega
        simp [hn,hs]
      · have hn':n%2=1:=by omega
        have hs:(n+1)%2=0:=by omega
        simp [hn',hs]

theorem walk_differ (v : V) (hd : hM.Differ hN v) (n : ℕ) : hM.Differ hN (hM.walkVertex hN v n) := by
  induction n with
  | zero => exact hd
  | succ n ih =>
      simpa only [walkVertex,walkState_succ] using hM.differ_step hN (hM.walkState hN v n) ih

theorem walkDart_mem_left (v : V) (hd : hM.Differ hN v) (n : ℕ) :
    (hM.walkDart hN v n).1∈M ↔ Even n := by
  have hs:=hM.walkState_color hN v n
  have hdiff:=hM.walk_differ hN v hd n
  change (hM.stepPort hN (hM.walkState hN v n)).1∈M ↔ _
  unfold stepPort
  rw [hs]
  by_cases hn:n%2=0
  · simp only [hn,decide_true,if_true]
    exact iff_of_true (hM.port_mem _) (Nat.even_iff.mpr hn)
  · simp only [hn,decide_false,Bool.false_eq_true,if_false]
    exact iff_of_false (hN.differing_port_not_mem hM _ (Ne.symm hdiff)) (fun he=>hn (Nat.even_iff.mp he))

theorem walkDart_mem_right (v : V) (hd : hM.Differ hN v) (n : ℕ) :
    (hM.walkDart hN v n).1∈N ↔ Odd n := by
  have hs:=hM.walkState_color hN v n
  have hdiff:=hM.walk_differ hN v hd n
  change (hM.stepPort hN (hM.walkState hN v n)).1∈N ↔ _
  unfold stepPort
  rw [hs]
  by_cases hn:n%2=0
  · simp only [hn,decide_true,if_true]
    exact iff_of_false (hM.differing_port_not_mem hN _ hdiff) (by rw [Nat.odd_iff]; omega)
  · simp only [hn,decide_false,Bool.false_eq_true,if_false]
    exact iff_of_true (hN.port_mem _) (by rw [Nat.odd_iff]; omega)

end PlanarHom.MultiGraph.PerfectMatching
