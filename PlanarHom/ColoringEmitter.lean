import PlanarHom.ColoringEmitterAllocation
import PlanarHom.ColoringEmitterAnswerBounds

/-! NEW complete numeric emitter/recovery machine interface. Source graph
isomorphism, planar realization, and counting correctness are separate joins. -/
namespace PlanarHom.ColoringEmitter
open Complexity ParsimoniousNorOneInThree

theorem certified_compile : FP formulaEncoding MixedCode.encoding compile ∧
    ∀f,(compile f).Valid 1 0 := ⟨fp_compile,compile_valid⟩

@[simp] theorem queries_length (f : NumericFormula) : (queries f).length=1 := rfl
@[simp] theorem componentCount_empty (n : ℕ) : componentCount (n,[])=0 := rfl
@[simp] theorem recover_empty (n : ℕ) (answers : List ℕ) :
    recover ((n,[]),answers)=2^n*answers.headD 0 := by
  simp [recover,unusedOriginal]

end PlanarHom.ColoringEmitter
