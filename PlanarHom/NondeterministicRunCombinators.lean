import PlanarHom.NondeterministicComputationTree
import Mathlib.Logic.Function.Iterate

/-!
# Deterministic prefixes of nondeterministic computations

A deterministic `Option`-valued transition system can be embedded as ordinary
nodes of a nondeterministic computation tree. Iterating those transitions adds
exactly the same amount to the tree's clock and does not change its accepting
count. The lemmas also allow a bound on a tree to be enlarged.
-/

namespace PlanarHom.NondeterministicComputationTree

universe u

/-- Any extra fuel preserves a bound on all computation branches. -/
theorem Bounded.add {Cfg : Type u} {view : Cfg → NodeView Cfg} {c : Cfg} {n : ℕ}
    (h : Bounded view c n) (k : ℕ) : Bounded view c (n + k) := by
  induction h with
  | reject halt => exact .reject halt
  | accept halt => exact .accept halt
  | ordinary step tail ih =>
      simpa only [Nat.add_right_comm] using Bounded.ordinary step ih
  | binary step left right ihl ihr =>
      simpa only [Nat.add_right_comm] using Bounded.binary step ihl ihr

/-- A larger clock remains a bound on every computation branch. -/
theorem Bounded.mono {Cfg : Type u} {view : Cfg → NodeView Cfg} {c : Cfg} {n m : ℕ}
    (h : Bounded view c n) (hnm : n ≤ m) : Bounded view c m := by
  simpa only [Nat.add_sub_of_le hnm] using h.add (m - n)

end PlanarHom.NondeterministicComputationTree

namespace PlanarHom.NondeterministicRunCombinators

open NondeterministicComputationTree

universe u v

variable {Cfg : Type u} {D : Type v}

/-- An iteration ending in a configuration has a successful first transition. -/
theorem iterate_succ_some (step : Cfg → Option Cfg) {c d : Cfg} {n : ℕ}
    (run : (fun x : Option Cfg => x.bind step)^[n + 1] (some c) = some d) :
    ∃ next, step c = some next ∧
      (fun x : Option Cfg => x.bind step)^[n] (some next) = some d := by
  rw [Function.iterate_succ_apply] at run
  change (fun x : Option Cfg => x.bind step)^[n] (step c) = some d at run
  cases hs : step c with
  | none =>
      rw [hs, Function.iterate_fixed (show (none : Option Cfg).bind step = none from rfl)]
        at run
      cases run
  | some next => exact ⟨next, rfl, by simpa only [hs] using run⟩

/-- An embedded deterministic prefix consumes one unit of fuel per transition. -/
theorem bounded_of_iterate (step : Cfg → Option Cfg) (view : D → NodeView D)
    (embed : Cfg → D)
    (ordinary : ∀ {c d}, step c = some d → view (embed c) = .ordinary (embed d))
    {c d : Cfg} {n fuel : ℕ}
    (run : (fun x : Option Cfg => x.bind step)^[n] (some c) = some d)
    (tail : Bounded view (embed d) fuel) : Bounded view (embed c) (n + fuel) := by
  induction n generalizing c with
  | zero =>
      have hcd : c = d := Option.some.inj run
      simpa only [hcd, Nat.zero_add] using tail
  | succ n ih =>
      obtain ⟨next, hs, hr⟩ := iterate_succ_some step run
      simpa only [Nat.add_right_comm] using Bounded.ordinary (ordinary hs) (ih hr)

/-- Deterministic prefixes preserve accepting multiplicity at the translated clock.
No halting or boundedness assumption is needed for the suffix. -/
theorem acceptingCount_of_iterate (step : Cfg → Option Cfg) (view : D → NodeView D)
    (embed : Cfg → D)
    (ordinary : ∀ {c d}, step c = some d → view (embed c) = .ordinary (embed d))
    {c d : Cfg} {n fuel : ℕ}
    (run : (fun x : Option Cfg => x.bind step)^[n] (some c) = some d) :
    acceptingCount view (n + fuel) (embed c) = acceptingCount view fuel (embed d) := by
  induction n generalizing c with
  | zero =>
      have hcd : c = d := Option.some.inj run
      simp only [hcd, Nat.zero_add]
  | succ n ih =>
      obtain ⟨next, hs, hr⟩ := iterate_succ_some step run
      rw [Nat.add_right_comm n 1 fuel]
      simpa only [acceptingCount, ordinary hs] using ih hr

end PlanarHom.NondeterministicRunCombinators
