import PlanarHom.Complexity
import PlanarHom.NondeterministicComputationTree

/-! # Binary nondeterministic finite-control multistack machines

The ordinary instructions are literal TM2 syntax. At a designated choice label,
a transition chooses one of two continuation labels and leaves all stack symbols
and finite registers unchanged. Both alternatives count separately even when the
continuation labels agree. Halting output `[true]` accepts; every other output
rejects. A halting instruction is charged one transition, just like every choice.
-/
namespace PlanarHom.NondeterministicTM2
open Turing Turing.TM2 Complexity NondeterministicComputationTree

structure Machine where
  core : TM2ComputableAux Bool Bool
  finiteAlphabet : ∀ k, Fintype (core.tm.Γ k)
  branch : core.tm.Λ → Option (core.tm.Λ × core.tm.Λ)

namespace Machine
abbrev Cfg (m : Machine) := m.core.tm.Cfg

def initial (m : Machine) (x : Bits) : m.Cfg :=
  initList m.core.tm (x.map m.core.inputAlphabet.symm)

def output (m : Machine) (c : m.Cfg) : Bits :=
  (c.stk m.core.tm.k₁).map m.core.outputAlphabet

def jump (m : Machine) (c : m.Cfg) (l : m.core.tm.Λ) : m.Cfg :=
  { c with l := some l }

def view (m : Machine) (c : m.Cfg) : NodeView m.Cfg :=
  match c.l with
  | none => if m.output c = [true] then .accept else .reject
  | some l => match m.branch l with
    | some (l₀,l₁) => .binary (m.jump c l₀) (m.jump c l₁)
    | none => .ordinary (stepAux (m.core.tm.m l) c.var c.stk)

end Machine
end PlanarHom.NondeterministicTM2
