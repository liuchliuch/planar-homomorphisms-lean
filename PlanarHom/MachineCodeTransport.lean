import PlanarHom.Complexity

/-! Reusing a machine under literal equality of its input codewords. -/

namespace PlanarHom.Complexity

open Turing

/-- A change in the mathematical type of valid inputs requires no machine step
when the serialized words are provably identical. This theorem supplies no
algorithm for `view`; it reuses the original input bits without modifying them. -/
noncomputable def transportInputComputer {α β γ : Type}
    (ea : BitEncoding α) (eb : BitEncoding β) (ec : BitEncoding γ)
    (view : α → β) (sameWords : ∀ a, eb.encode (view a) = ea.encode a)
    {f : β → γ} (computer : TM2ComputableInPolyTime eb.toFinEncoding ec.toFinEncoding f) :
    TM2ComputableInPolyTime ea.toFinEncoding ec.toFinEncoding (f ∘ view) where
  toTM2ComputableAux := computer.toTM2ComputableAux
  time := computer.time
  outputsFun a := {
    steps := (computer.outputsFun (view a)).steps
    evals_in_steps := by
      have h := (computer.outputsFun (view a)).evals_in_steps
      simpa only [BitEncoding.toFinEncoding,sameWords,Function.comp_apply] using h
    steps_le_m := by
      have h := (computer.outputsFun (view a)).steps_le_m
      simpa only [BitEncoding.toFinEncoding,sameWords] using h }

/-- Proposition-valued wrapper for literal input-codeword transport. -/
theorem FP.transportInput {α β γ : Type}
    {ea : BitEncoding α} {eb : BitEncoding β} {ec : BitEncoding γ}
    (view : α → β) (sameWords : ∀ a, eb.encode (view a) = ea.encode a)
    {f : β → γ} (hf : FP eb ec f) : FP ea ec (f ∘ view) := by
  obtain ⟨computer⟩ := hf
  exact ⟨transportInputComputer ea eb ec view sameWords computer⟩

end PlanarHom.Complexity
