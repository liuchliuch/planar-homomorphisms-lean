import PlanarHom.DynamicMatrixFamilySource
import PlanarHom.GraphCodeNormalization

/-! Runtime parameter promises: canonical parameter words and unrestricted successful raw graph words. -/
noncomputable section
namespace PlanarHom.ParameterizedMatrixEvaluation
open Complexity Complexity.MixedCode FiniteLanguageAliases ArithmeticCircuitPrimitives PairProjectionMachines
variable {X K : Type} [Field K] [Algebra ℚ K] {dimension q bt ut : ℕ}

/-- The parameter uses its exact ex codeword. The graph component retains every
original successful raw word, including alternate noncanonical graph encodings. -/
def inputEncoding (ex : BitEncoding X) : BitEncoding (X × BitEncoding.ValidWord MixedCode.encoding) :=
  ex.prod (BitEncoding.ValidWord.encoding MixedCode.encoding)

def answer (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (B : X → Matrix (Fin q) (Fin q) K) (p : X × MixedCode) : K :=
  totalEvaluation (appendOne M (B p.1)) U w p.2

/-- No normalizer for an arbitrary parameter encoding is assumed. Canonical
parameter words are paired with all raw graph words in the ordinary planar promise. -/
def problem (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (B : X → Matrix (Fin q) (Fin q) K) (allowed : X → Prop) : PromiseProblem :=
  ⟨fun raw => ∃ p : X × BitEncoding.ValidWord MixedCode.encoding,
      (inputEncoding ex).encode p = raw ∧ allowed p.1 ∧ p.2.value.PlanarValid (bt+1) ut,
    encodedFunction (ex.prod MixedCode.encoding) (numberFieldEncoding basis) (answer M U w B) []⟩

theorem decode_raw_input (ex : BitEncoding X) (p : X × BitEncoding.ValidWord MixedCode.encoding) :
    (ex.prod MixedCode.encoding).decode ((inputEncoding ex).encode p) = some (p.1, p.2.value) := by
  simp [inputEncoding, BitEncoding.prod, BitEncoding.ValidWord.encoding, ex.decode_encode]

theorem value_raw_input (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (B : X → Matrix (Fin q) (Fin q) K) (allowed : X → Prop)
    (p : X × BitEncoding.ValidWord MixedCode.encoding) :
    (problem basis ex M U w B allowed).value ((inputEncoding ex).encode p) =
      (numberFieldEncoding basis).encode (answer M U w B (p.1,p.2.value)) := by
  simp only [problem, encodedFunction, decode_raw_input]

/-- Exact characterization in terms of the original parameter and raw graph words. -/
theorem valid_iff_rawGraph (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (w : Fin q → K)
    (B : X → Matrix (Fin q) (Fin q) K) (allowed : X → Prop) (raw : Bits) :
    (problem basis ex M U w B allowed).valid raw ↔
      ∃ x rawGraph, raw = BitEncoding.frame (ex.encode x) ++ rawGraph ∧ allowed x ∧
        MixedCode.PlanarInput (bt+1) ut rawGraph := by
  constructor
  · rintro ⟨⟨x,g⟩, hword, hx, hg⟩
    exact ⟨x,g.val,hword.symm,hx,g.value,BitEncoding.ValidWord.decode_raw g,hg⟩
  · rintro ⟨x,rawGraph,hword,hx,g,hd,hg⟩
    let gw : BitEncoding.ValidWord MixedCode.encoding := ⟨rawGraph,⟨g,hd⟩⟩
    refine ⟨(x,gw),hword.symm,hx,?_⟩
    have hv : BitEncoding.ValidWord.value gw = g := BitEncoding.ValidWord.value_eq (w := gw) hd
    change gw.value.PlanarValid (bt+1) ut
    rw [hv]
    exact hg

/-- Only the raw graph is normalized; the exact parameter word passes through
ordinary projections and pairing before its supplied FP evaluator runs. -/
theorem fp_normalize (ex : BitEncoding X) : FP (inputEncoding ex) (ex.prod MixedCode.encoding)
    (fun p => (p.1,p.2.value)) :=
  (fp_fst ex (BitEncoding.ValidWord.encoding MixedCode.encoding)).pair
    ((fp_snd ex (BitEncoding.ValidWord.encoding MixedCode.encoding)).comp ⟨MixedCode.normalizer⟩)

/-- Optional actual representation transport when a parameter normalizer is
available. Only the parameter word is canonicalized; the original raw graph word
is preserved byte for byte in the resulting inputEncoding representation. -/
theorem fp_normalize_parameter (ex : BitEncoding X) (hx : BitEncoding.Normalizer ex) :
    FP ((BitEncoding.ValidWord.encoding ex).prod (BitEncoding.ValidWord.encoding MixedCode.encoding))
      (inputEncoding ex) (fun p => (p.1.value,p.2)) :=
  ((fp_fst (BitEncoding.ValidWord.encoding ex) (BitEncoding.ValidWord.encoding MixedCode.encoding)).comp ⟨hx⟩).pair
    (fp_snd (BitEncoding.ValidWord.encoding ex) (BitEncoding.ValidWord.encoding MixedCode.encoding))

end PlanarHom.ParameterizedMatrixEvaluation
