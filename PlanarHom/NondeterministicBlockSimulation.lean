import PlanarHom.NondeterministicRunCombinators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Costed deterministic blocks in nondeterministic computation trees

The simulation relation is indexed by remaining source time. Every target edge
inside a block is an actual ordinary transition. Binary blocks end in one actual
binary transition, so coincident continuations retain both labelled choices.
-/
namespace PlanarHom.NondeterministicBlockSimulation
open NondeterministicComputationTree

universe u v
variable {C : Type u} {D : Type v}

/-- A finite sequence consisting entirely of actual ordinary transitions. -/
inductive OrdinaryRun (view : D → NodeView D) : ℕ → D → D → Prop where
  | nil (c) : OrdinaryRun view 0 c c
  | cons {n c next d} (step : view c = .ordinary next)
      (tail : OrdinaryRun view n next d) : OrdinaryRun view (n+1) c d

namespace OrdinaryRun
variable {view : D → NodeView D} {a b c : D} {n m fuel : ℕ}

theorem trans (h : OrdinaryRun view n a b) (k : OrdinaryRun view m b c) :
    OrdinaryRun view (n+m) a c := by
  induction h with
  | nil => simpa using k
  | cons step tail ih => simpa [Nat.add_right_comm] using cons step (ih k)

theorem bounded (h : OrdinaryRun view n a b) (tail : Bounded view b fuel) :
    Bounded view a (n+fuel) := by
  induction h with
  | nil => simpa using tail
  | cons step run ih => simpa [Nat.add_right_comm] using Bounded.ordinary step (ih tail)

theorem count (h : OrdinaryRun view n a b) :
    acceptingCount view (n+fuel) a = acceptingCount view fuel b := by
  induction h with
  | nil => simp
  | cons step run ih => simpa [Nat.add_right_comm, acceptingCount, step] using ih

/-- Convert successful deterministic machine execution to its ordinary edges. -/
theorem of_iterate {E : Type u} (step : E → Option E) (embed : E → D)
    (ordinary : ∀ {a b}, step a = some b → view (embed a) = .ordinary (embed b))
    {a b : E} {n : ℕ}
    (run : (fun x : Option E => x.bind step)^[n] (some a) = some b) :
    OrdinaryRun view n (embed a) (embed b) := by
  induction n generalizing a with
  | zero => cases Option.some.inj run; exact .nil _
  | succ n ih =>
    obtain ⟨next, hs, hr⟩ := NondeterministicRunCombinators.iterate_succ_some step run
    exact .cons (ordinary hs) (ih hr)

end OrdinaryRun

/-- Local proof obligations for a costed, multiplicity-preserving compiler.
`Related n` can include a materialized-space bound with `n` source steps left.
Every obligation concerns the actual target view and an actual finite run. -/
structure Simulation (source : C → NodeView C) (target : D → NodeView D) (cost : ℕ) where
  Related : ℕ → C → D → Prop
  reject : ∀ {n c d}, Related n c d → source c = .reject →
    ∃ k e, k ≤ cost ∧ OrdinaryRun target k d e ∧ target e = .reject
  accept : ∀ {n c d}, Related n c d → source c = .accept →
    ∃ k e, k ≤ cost ∧ OrdinaryRun target k d e ∧ target e = .accept
  ordinary : ∀ {n c next d}, Related (n+1) c d → source c = .ordinary next →
    ∃ k e, k ≤ cost ∧ OrdinaryRun target k d e ∧ Related n next e
  binary : ∀ {n c left right d}, Related (n+1) c d → source c = .binary left right →
    ∃ k e dl dr, k+1 ≤ cost ∧ OrdinaryRun target k d e ∧
      target e = .binary dl dr ∧ Related n left dl ∧ Related n right dr

namespace Simulation
variable {source : C → NodeView C} {target : D → NodeView D} {cost : ℕ}

/-- Every source branch halts, every target branch halts, and the accepting
counts agree at the common polynomially enlarged clock. No accepting-only
termination hypothesis or choice of distinct successor configurations is used. -/
theorem correct (S : Simulation source target cost) {n : ℕ} {c : C}
    (h : Bounded source c n) {d : D} (related : S.Related n c d) :
    Bounded target d ((n+1)*cost) ∧
      acceptingCount target ((n+1)*cost) d = acceptingCount source n c := by
  induction h generalizing d with
  | @reject c n hv =>
    obtain ⟨k,e,hk,hr,he⟩ := S.reject related hv
    have hb : Bounded target d k := by simpa using hr.bounded (Bounded.reject he (n := 0))
    have hk' : k ≤ (n+1)*cost := hk.trans (by nlinarith)
    refine ⟨hb.mono hk', ?_⟩
    rw [hb.acceptingCount_eq_of_le hk']
    have hc := hr.count (fuel := 0)
    simpa [acceptingCount,he,acceptingCount_reject source hv] using hc
  | @accept c n hv =>
    obtain ⟨k,e,hk,hr,he⟩ := S.accept related hv
    have hb : Bounded target d k := by simpa using hr.bounded (Bounded.accept he (n := 0))
    have hk' : k ≤ (n+1)*cost := hk.trans (by nlinarith)
    refine ⟨hb.mono hk', ?_⟩
    rw [hb.acceptingCount_eq_of_le hk']
    have hc := hr.count (fuel := 0)
    simpa [acceptingCount,he,acceptingCount_accept source hv] using hc
  | @ordinary c next n hv tail ih =>
    obtain ⟨k,e,hk,hr,he⟩ := S.ordinary related hv
    obtain ⟨hb,hc⟩ := ih he
    have hb' := hr.bounded hb
    have hk' : k+(n+1)*cost ≤ (n+1+1)*cost := by nlinarith
    refine ⟨hb'.mono hk', ?_⟩
    rw [hb'.acceptingCount_eq_of_le hk',hr.count,hc]
    simp [acceptingCount,hv]
  | @binary c left right n hv hl hr ihl ihr =>
    obtain ⟨k,e,dl,dr,hk,run,he,hrel,hrr⟩ := S.binary related hv
    obtain ⟨hbl,hcl⟩ := ihl hrel
    obtain ⟨hbr,hcr⟩ := ihr hrr
    have hb' := run.bounded (Bounded.binary he hbl hbr)
    have hk' : k+((n+1)*cost+1) ≤ (n+1+1)*cost := by nlinarith
    refine ⟨hb'.mono hk', ?_⟩
    rw [hb'.acceptingCount_eq_of_le hk',run.count]
    simp [acceptingCount,he,hv,hcl,hcr]

end Simulation
end PlanarHom.NondeterministicBlockSimulation
