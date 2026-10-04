import PlanarHom.MachineCodeTransport

/-! A proof-only change of output type when every actual output word is identical. -/
namespace PlanarHom.Complexity
open Turing

/-- Reuse the exact TM2, time polynomial, and execution when the target codewords
are literally equal on all inputs. This contains no runtime application of a
host-language conversion and makes no claim about arbitrary malformed words. -/
noncomputable def transportOutputComputer {α β γ : Type}
    (ea : BitEncoding α) (eb : BitEncoding β) (ec : BitEncoding γ)
    {f : α→β} {g : α→γ} (sameWords : ∀ a, eb.encode (f a)=ec.encode (g a))
    (computer : TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding f) :
    TM2ComputableInPolyTime ea.toFinEncoding ec.toFinEncoding g where
  toTM2ComputableAux := computer.toTM2ComputableAux
  time := computer.time
  outputsFun a := {
    steps := (computer.outputsFun a).steps
    evals_in_steps := by
      have h := (computer.outputsFun a).evals_in_steps
      simpa only [BitEncoding.toFinEncoding,sameWords] using h
    steps_le_m := (computer.outputsFun a).steps_le_m }

theorem FP.transportOutput {α β γ : Type}
    {ea : BitEncoding α} {eb : BitEncoding β} {ec : BitEncoding γ}
    {f : α→β} {g : α→γ} (hf : FP ea eb f)
    (sameWords : ∀ a, eb.encode (f a)=ec.encode (g a)) : FP ea ec g := by
  obtain ⟨computer⟩ := hf
  exact ⟨transportOutputComputer ea eb ec sameWords computer⟩

end PlanarHom.Complexity
