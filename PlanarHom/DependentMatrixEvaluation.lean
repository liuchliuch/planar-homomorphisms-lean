import PlanarHom.ParameterizedMatrixEvaluation
import PlanarHom.DependentEncodingMachines

/-! Variable-field target promises with explicit prescribed output encodings. -/
noncomputable section
namespace PlanarHom.DependentMatrixEvaluation
open Complexity Complexity.MixedCode FiniteLanguageAliases
variable {L X : Type} [Field L] (K : X → Type) [∀ x, Field (K x)]
variable (ex : BitEncoding X) (output : ∀ x, BitEncoding (K x)) (inclusion : ∀ x, L →+* K x)
variable {q bt ut : ℕ}
variable (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
variable (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop)

/-- Canonical ex parameter followed by the unrestricted successful original graph word. -/
abbrev inputEncoding := ParameterizedMatrixEvaluation.inputEncoding (X := X)

def answer (p : X × MixedCode) : Bits :=
  (output p.1).encode (totalEvaluation
    (appendOne (fun l i j => inclusion p.1 (M l i j)) (B p.1))
    (fun l i => inclusion p.1 (U l i)) (fun i => inclusion p.1 (w i)) p.2)

/-- The target output uses exactly output x, without a parameter frame. Arithmetic
may use a different internal basis codec only through a separately compiled conversion. -/
def problem : PromiseProblem :=
  ⟨fun raw => ∃ p : X × BitEncoding.ValidWord MixedCode.encoding,
      (inputEncoding ex).encode p = raw ∧ allowed p.1 ∧ p.2.value.PlanarValid (bt+1) ut,
    encodedFunction (ex.prod MixedCode.encoding) BitEncoding.bits (answer K output inclusion M U w B) []⟩

theorem value_raw_input (p : X × BitEncoding.ValidWord MixedCode.encoding) :
    (problem K ex output inclusion M U w B allowed).value ((inputEncoding ex).encode p) =
      answer K output inclusion M U w B (p.1,p.2.value) := by
  simp only [problem, encodedFunction, ParameterizedMatrixEvaluation.decode_raw_input]
  rfl

theorem valid_iff_rawGraph (raw : Bits) :
    (problem K ex output inclusion M U w B allowed).valid raw ↔
      ∃ x rawGraph, raw = BitEncoding.frame (ex.encode x) ++ rawGraph ∧ allowed x ∧
        MixedCode.PlanarInput (bt+1) ut rawGraph := by
  constructor
  · rintro ⟨⟨x,g⟩,hword,hx,hg⟩
    exact ⟨x,g.val,hword.symm,hx,g.value,BitEncoding.ValidWord.decode_raw g,hg⟩
  · rintro ⟨x,rawGraph,hword,hx,g,hd,hg⟩
    let gw : BitEncoding.ValidWord MixedCode.encoding := ⟨rawGraph,⟨g,hd⟩⟩
    refine ⟨(x,gw),hword.symm,hx,?_⟩
    have hv : gw.value = g := BitEncoding.ValidWord.value_eq (w := gw) hd
    change gw.value.PlanarValid (bt+1) ut
    rw [hv]
    exact hg

end PlanarHom.DependentMatrixEvaluation
