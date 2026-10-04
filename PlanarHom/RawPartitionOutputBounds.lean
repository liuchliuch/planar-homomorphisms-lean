import PlanarHom.PartitionOutputBounds
import PlanarHom.CodecDecodingBounds

/-! Actual partition-answer size for arbitrary successfully decoded raw inputs. -/

noncomputable section
namespace PlanarHom.PartitionOutputBounds
open Complexity

/-- Polynomial answer length on every valid decoded word, including noncanonical encodings.
This uses only a proved size bridge, and does not claim a raw normalization machine. -/
theorem exists_polynomial_raw_mixed_evaluation_length_bound
    {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
    {dimension binaryTypes unaryTypes : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes → Matrix C C K) (U : Fin unaryTypes → C → K) (w : C → K) :
    ∃ p : Polynomial ℕ, ∀ (bits : Bits) (g : MixedCode) (valid : g.Valid binaryTypes unaryTypes),
      MixedCode.encoding.decode bits = some g →
      ((numberFieldEncoding basis).encode (g.evaluate valid M U w)).length ≤ p.eval bits.length := by
  obtain ⟨p, hp⟩ := exists_polynomial_mixed_evaluation_length_bound basis M U w
  refine ⟨p.comp (Polynomial.C 49 * (Polynomial.X + Polynomial.C 1)), ?_⟩
  intro bits g valid hdecode
  apply (hp g valid).trans
  simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X] using
    MachineComposition.natPolynomial_monotone p (MixedCode.decode_length_bound bits g hdecode)

end PlanarHom.PartitionOutputBounds
