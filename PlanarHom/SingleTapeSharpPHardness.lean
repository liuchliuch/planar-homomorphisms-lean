import PlanarHom.SharpPBridge
import PlanarHom.SingleTapeToNondeterministicTM2

/-! # Hardness for conventional single-tape nondeterministic counting

The source definition uses mathlib's actual tape and local read/write/move
instructions. The explicit compiler preserves accepting counts and bounds every
path by twice the source time plus linear input-loading overhead. Thus a proved
certificate-class hardness theorem entails hardness for this independent
single-tape accepting-path class; no converse machine-model simulation is used.
-/
namespace PlanarHom.SingleTapeNondeterministic
open Complexity

/-- Hardness for binary-choice, finite-state, finite-alphabet single-tape
nondeterministic machines, under the existing exact binary oracle reductions. -/
def SingleTapeSharpPHard (oracle : Bits → Bits) : Prop :=
  ∀ f : Bits → ℕ, SingleTapeSharpP f →
    TuringReduces (fun x => BitEncoding.nat.encode (f x)) oracle

theorem SingleTapeSharpP.certificateSharpP {f : Bits → ℕ} (h : SingleTapeSharpP f) :
    CertificateSharpP f := h.sharpP.certificateSharpP

end PlanarHom.SingleTapeNondeterministic

namespace PlanarHom.Complexity

theorem SharpPHard.singleTapeSharpPHard {oracle : Bits → Bits} (h : SharpPHard oracle) :
    SingleTapeNondeterministic.SingleTapeSharpPHard oracle :=
  fun f hf => h f hf.sharpP

/-- The complete source-facing hardness bridge, using actual compilers in both
counting conventions and no assumed single-tape model equivalence. -/
theorem CertificateSharpPHard.singleTapeSharpPHard {oracle : Bits → Bits}
    (h : CertificateSharpPHard oracle) : SingleTapeNondeterministic.SingleTapeSharpPHard oracle :=
  h.sharpPHard.singleTapeSharpPHard

end PlanarHom.Complexity
