import PlanarHom.NondeterministicCertificateBridge
import PlanarHom.CertificateNondeterministicCompiler

/-! # Constructive machine-model bridge for exact counting classes

Both directions use actual finite-control compilers. The forward compiler
replays one canonical padded bit per transition; the reverse compiler physically
materializes the certificate bound, branches once per witness bit, and runs the
given deterministic verifier. Their accepting counts agree exactly.
-/
namespace PlanarHom.Complexity

/-- Independent finite-alphabet multistack accepting-path counting agrees
exactly with the existing polynomial-length binary-certificate class. -/
theorem sharpP_iff_certificateSharpP (f : Bits → ℕ) :
    SharpP f ↔ CertificateSharpP f :=
  ⟨SharpP.certificateSharpP,CertificateSharpP.sharpP⟩

/-- The machine/certificate equivalence preserves the existing binary natural
output code and the exact oracle-TM2 reduction convention. -/
theorem sharpPHard_iff_certificateSharpPHard (oracle : Bits → Bits) :
    SharpPHard oracle ↔ CertificateSharpPHard oracle := by
  constructor
  · intro h f hf
    exact h f hf.sharpP
  · exact CertificateSharpPHard.sharpPHard

end PlanarHom.Complexity
