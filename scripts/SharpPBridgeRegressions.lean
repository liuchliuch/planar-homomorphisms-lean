import PlanarHom.SharpPBridge

namespace PlanarHom.SharpPBridgeRegressions
open Complexity

example (f : Bits → ℕ) : SharpP f ↔ CertificateSharpP f := sharpP_iff_certificateSharpP f
example (g : Bits → Bits) : SharpPHard g ↔ CertificateSharpPHard g :=
  sharpPHard_iff_certificateSharpPHard g

theorem true_verifier_fp : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool
    (fun _ : Bits × Bits => true) :=
  fp_const _ _ true

theorem false_verifier_fp : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool
    (fun _ : Bits × Bits => false) :=
  fp_const _ _ false

example (p : Polynomial ℕ) (x : Bits) :
    (CertificateNondeterministicCompiler.compile p (fun _ => true) true_verifier_fp).count x =
      2 ^ p.eval x.length := by
  rw [CertificateNondeterministicCompiler.count_eq_certificateCount]
  simp [certificateCount]

example (p : Polynomial ℕ) (x : Bits) :
    (CertificateNondeterministicCompiler.compile p (fun _ => false) false_verifier_fp).count x = 0 := by
  rw [CertificateNondeterministicCompiler.count_eq_certificateCount]
  simp [certificateCount]

-- The zero-bit certificate is one possible witness, not zero witnesses.
example (x : Bits) :
    (CertificateNondeterministicCompiler.compile 0 (fun _ => true) true_verifier_fp).count x = 1 := by
  rw [CertificateNondeterministicCompiler.count_eq_certificateCount]
  simp [certificateCount]

example (p : Polynomial ℕ) (x : Bits) :
    NondeterministicComputationTree.Bounded
      (CertificateNondeterministicCompiler.compile p (fun _ => false) false_verifier_fp).machine.view
      ((CertificateNondeterministicCompiler.compile p (fun _ => false) false_verifier_fp).machine.initial x)
      ((CertificateNondeterministicCompiler.compile p (fun _ => false) false_verifier_fp).time.eval x.length) :=
  (CertificateNondeterministicCompiler.compile p (fun _ => false) false_verifier_fp).halts x

#check CertificateNondeterministicCompiler.compile
#check CertificateNondeterministicCompiler.count_eq_certificateCount
#check sharpP_iff_certificateSharpP
#check sharpPHard_iff_certificateSharpPHard
#print axioms sharpP_iff_certificateSharpP
#print axioms sharpPHard_iff_certificateSharpPHard

end PlanarHom.SharpPBridgeRegressions
