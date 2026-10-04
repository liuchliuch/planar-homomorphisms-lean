import PlanarHom.CountingCookLevinBooleanTables

/-! Fixed-length NOR blocks give every output a predetermined register address.
Padding is deterministic and therefore introduces no counting multiplicity. -/
namespace PlanarHom.CountingCookLevin
open Complexity PairProjectionMachines

namespace Expr

/-- Double negation makes every template end in a genuine fresh output gate. -/
def copyOutput {V : Type} (e : Expr V) : Expr V := e.neg.neg

@[simp] theorem copyOutput_eval {V : Type} (e : Expr V) (ρ : V → Bool) :
    e.copyOutput.eval ρ=e.eval ρ := by simp [copyOutput]

@[simp] theorem copyOutput_gates {V : Type} (e : Expr V) : e.copyOutput.gates=4*e.gates+3 := by
  simp only [copyOutput,neg,gates]
  omega

theorem copyOutput_output {V : Type} (e : Expr V) (start : ℕ) (ρ : V → ℕ) :
    e.copyOutput.output start ρ=start+4*(e.copyOutput.gates-1) := by
  simp only [copyOutput,neg,output,gates]
  omega

/-- Pad before evaluating, so the final output always occupies the first
register produced by the block's last gate. -/
def regularBlock {V : Type} (e : Expr V) (C start : ℕ) (ρ : V → ℕ) : NorGates :=
  List.replicate (C-e.copyOutput.gates) (0,0) ++
    e.copyOutput.emit (start+4*(C-e.copyOutput.gates)) ρ

theorem regularBlock_length {V : Type} (e : Expr V) (C start : ℕ) (ρ : V → ℕ)
    (hC : e.copyOutput.gates≤C) : (e.regularBlock C start ρ).length=C := by
  simp only [regularBlock,List.length_append,List.length_replicate,emit_length]
  omega

/-- The fixed output address is valid and computes the exact original template. -/
theorem regularBlock_correct {V : Type} (e : Expr V) (C : ℕ) (ρ : V → ℕ) (xs : List Bool)
    (hC : e.copyOutput.gates≤C) (hρ : ∀ v,ρ v<xs.length) :
    readBit (runNor (e.regularBlock C xs.length ρ) xs) (xs.length+4*(C-1))=
      e.eval (fun v => readBit xs (ρ v)) := by
  let pad := List.replicate (C-e.copyOutput.gates) (0,0)
  let ys := runNor pad xs
  have hlen : ys.length=xs.length+4*(C-e.copyOutput.gates) := by simp [ys,pad]
  have hρ' : ∀ v,ρ v<ys.length := fun v => (hρ v).trans_le (by rw [hlen]; omega)
  have ho : e.copyOutput.output ys.length ρ=xs.length+4*(C-1) := by
    rw [copyOutput_output,hlen]
    have hp : 0<e.copyOutput.gates := by rw [copyOutput_gates]; omega
    omega
  simp only [regularBlock,runNor_append]
  rw [← hlen,← ho]
  change readBit (runNor (e.copyOutput.emit ys.length ρ) ys) (e.copyOutput.output ys.length ρ)=_
  rw [emit_correct _ _ _ hρ',copyOutput_eval]
  exact e.eval_congr _ _ (fun v => runNor_read_old pad xs _ (hρ v))

/-- A regular block has a real typed polynomial-time emitter; its fixed padding
and local truth table are part of the source-machine program. -/
theorem fp_regularBlock {d : ℕ} (e : Expr (Fin d)) (C : ℕ) :
    FP (templateInputEncoding d) (BitEncoding.nat.prod BitEncoding.nat).list
      (fun p => e.regularBlock C p.1 p.2) := by
  let eg := BitEncoding.nat.prod BitEncoding.nat
  have hp := fp_const (templateInputEncoding d) eg.list (List.replicate (C-e.copyOutput.gates) (0,0))
  have he := (fp_template_offset d (4*(C-e.copyOutput.gates))).comp e.copyOutput.fp_emit
  exact (hp.pair he).comp (ListMutationMachines.fp_append eg)

end Expr
end PlanarHom.CountingCookLevin
