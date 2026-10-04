import PlanarHom.TM2SingleTapeCounting
import PlanarHom.SingleTapeSharpPHardness

/-! # Equality with conventional single-tape accepting-path #P

The reverse compiler is an actual finite-control, finite-alphabet, binary-choice
single-tape machine, initialized on the literal binary input. Its polynomial
bounds every accepting and rejecting computation and preserves the exact count.
Together with the earlier forward compiler and certificate bridge, this proves
all three counting conventions equivalent without a model-equivalence premise.
-/
namespace PlanarHom.Complexity
open SingleTapeNondeterministic

/-- The concrete reverse compiler supplies conventional single-tape membership. -/
theorem SharpP.singleTapeSharpP {f : Bits → ℕ} (h : SharpP f) : SingleTapeSharpP f := by
  obtain ⟨M,hM⟩ := h
  exact ⟨TM2SingleTapeCounting.polynomialCompile M,fun x =>
    (hM x).trans (TM2SingleTapeCounting.polynomialCompile_count M x).symm⟩

/-- Exact-length certificate membership entails conventional accepting-path #P. -/
theorem CertificateSharpP.singleTapeSharpP {f : Bits → ℕ} (h : CertificateSharpP f) :
    SingleTapeSharpP f := h.sharpP.singleTapeSharpP

theorem sharpP_iff_singleTapeSharpP (f : Bits → ℕ) : SharpP f ↔ SingleTapeSharpP f :=
  ⟨SharpP.singleTapeSharpP,SingleTapeSharpP.sharpP⟩

theorem certificateSharpP_iff_singleTapeSharpP (f : Bits → ℕ) :
    CertificateSharpP f ↔ SingleTapeSharpP f :=
  ⟨CertificateSharpP.singleTapeSharpP,SingleTapeSharpP.certificateSharpP⟩

end PlanarHom.Complexity

namespace PlanarHom.SingleTapeNondeterministic
open Complexity

theorem SingleTapeSharpPHard.sharpPHard {oracle : Bits → Bits}
    (h : SingleTapeSharpPHard oracle) : SharpPHard oracle :=
  fun f hf => h f hf.singleTapeSharpP

theorem SingleTapeSharpPHard.certificateSharpPHard {oracle : Bits → Bits}
    (h : SingleTapeSharpPHard oracle) : CertificateSharpPHard oracle :=
  fun f hf => h f hf.singleTapeSharpP

end PlanarHom.SingleTapeNondeterministic

namespace PlanarHom.Complexity
open SingleTapeNondeterministic

theorem sharpPHard_iff_singleTapeSharpPHard (oracle : Bits → Bits) :
    SharpPHard oracle ↔ SingleTapeSharpPHard oracle :=
  ⟨SharpPHard.singleTapeSharpPHard,SingleTapeSharpPHard.sharpPHard⟩

theorem certificateSharpPHard_iff_singleTapeSharpPHard (oracle : Bits → Bits) :
    CertificateSharpPHard oracle ↔ SingleTapeSharpPHard oracle :=
  ⟨CertificateSharpPHard.singleTapeSharpPHard,SingleTapeSharpPHard.certificateSharpPHard⟩

end PlanarHom.Complexity
