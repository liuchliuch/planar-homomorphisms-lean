import PlanarHom.CertificateGeneratorMachine
import PlanarHom.CertificateWordCount

/-! Exact path multiplicity and a bound on every branch of the literal certificate
compiler. The branch recurrence ranges over all physically generated witnesses. -/
namespace PlanarHom.CertificateGeneratorMachine
noncomputable section
open Turing Turing.TM2 Complexity MachineComposition NondeterministicComputationTree
open NondeterministicRunCombinators CertificateWordCount

variable (a b : TM2ComputableAux Bool Bool)
variable (ha : ∀ k, Fintype (a.tm.Γ k)) (hb : ∀ k, Fintype (b.tm.Γ k))

theorem generate_correct (x : Bits) (total vtime : ℕ) (V : Bits → Bool)
    (verify : ∀ w : Bits, w.length = total →
      TM2OutputsInTime b.tm ((BitEncoding.frame x++w).map b.inputAlphabet.symm)
        (some ([V w].map b.outputAlphabet.symm)) vtime)
    (n : ℕ) (w : Bits) (hlen : n+w.length = total) :
    Bounded (M a b ha hb).view
      (stage a b .generate (Computability.unaryEncodeNat n) w (BitEncoding.frame x).reverse)
      (3*n+(BitEncoding.frame x).length+2+vtime) ∧
    acceptingCount (M a b ha hb).view (3*n+(BitEncoding.frame x).length+2+vtime)
      (stage a b .generate (Computability.unaryEncodeNat n) w (BitEncoding.frame x).reverse) =
      bitsWordCount V n w := by
  induction n generalizing w with
  | zero =>
    have hh := verifier_correct a b ha hb (BitEncoding.frame x++w) (V w) vtime
      (verify w (by omega))
    have hr := restore_bounded a b ha hb (BitEncoding.frame x).reverse w vtime
      (by simpa using hh.1)
    have hc := restore_count a b ha hb (BitEncoding.frame x).reverse w vtime
    have ht := Bounded.ordinary (generate_nil a b ha hb w (BitEncoding.frame x).reverse) hr
    constructor
    · simp only [Computability.unaryEncodeNat,Nat.mul_zero,Nat.zero_add]
      convert ht using 1
      simp only [List.length_reverse]
      omega
    · rw [show 3*0+(BitEncoding.frame x).length+2+vtime =
          ((BitEncoding.frame x).reverse.length+1+vtime)+1 by simp; omega]
      simp only [Computability.unaryEncodeNat,acceptingCount,generate_nil]
      rw [hc]
      simpa [bitsWordCount] using hh.2
  | succ n ih =>
    have hf := ih (false::w) (by simp only [List.length_cons]; omega)
    have ht := ih (true::w) (by simp only [List.length_cons]; omega)
    have hbnd := Bounded.ordinary
      (generate_cons a b ha hb true (Computability.unaryEncodeNat n) w (BitEncoding.frame x).reverse)
      (Bounded.binary (choose_view a b ha hb (Computability.unaryEncodeNat n) w (BitEncoding.frame x).reverse)
        (Bounded.ordinary (push_view a b ha hb false (Computability.unaryEncodeNat n) w (BitEncoding.frame x).reverse) hf.1)
        (Bounded.ordinary (push_view a b ha hb true (Computability.unaryEncodeNat n) w (BitEncoding.frame x).reverse) ht.1))
    have he : 3*(n+1)+(BitEncoding.frame x).length+2+vtime =
      ((3*n+(BitEncoding.frame x).length+2+vtime)+1)+1+1 := by omega
    constructor
    · rw [he]
      exact hbnd
    · rw [he]
      simp only [Computability.unaryEncodeNat,acceptingCount,generate_cons,choose_view,push_view]
      rw [hf.2,ht.2]
      rfl

/-- Every generated witness runs through the actual verifier; rejecting witnesses
are included in the time bound, while only accepting leaves contribute to the count. -/
theorem run_correct (x : Bits) (n aprep vtime : ℕ) (V : Bits → Bool)
    (prep : TM2OutputsInTime a.tm (x.map a.inputAlphabet.symm)
      (some ((BitEncoding.frame x++Computability.unaryEncodeNat n).map a.outputAlphabet.symm)) aprep)
    (verify : ∀ w : Bits, w.length = n →
      TM2OutputsInTime b.tm ((BitEncoding.frame x++w).map b.inputAlphabet.symm)
        (some ([V w].map b.outputAlphabet.symm)) vtime) :
    Bounded (M a b ha hb).view ((M a b ha hb).initial x)
      (aprep+3*x.length+4+3*n+vtime) ∧
    acceptingCount (M a b ha hb).view (aprep+3*x.length+4+3*n+vtime)
      ((M a b ha hb).initial x) =
      Fintype.card {w : Fin n → Bool // V (List.ofFn w) = true} := by
  have hg := generate_correct a b ha hb x n vtime V verify n [] (by simp)
  let suffix := x.length+1+(3*n+(BitEncoding.frame x).length+2+vtime)
  have hs : Bounded (M a b ha hb).view
      (stage a b .scan (BitEncoding.frame x++Computability.unaryEncodeNat n) [] []) suffix := by
    exact scan_bounded a b ha hb x (Computability.unaryEncodeNat n) [] _ (by simpa using hg.1)
  have hsc : acceptingCount (M a b ha hb).view suffix
      (stage a b .scan (BitEncoding.frame x++Computability.unaryEncodeNat n) [] []) =
      bitsWordCount V n [] := by
    rw [scan_count]
    simpa using hg.2
  have hprep := bounded_of_iterate a.tm.step (M a b ha hb).view (leftCfg a.tm b.tm)
    (fun {c d} => left_view a b ha hb c d) prep.evals_in_steps
    (show Bounded (M a b ha hb).view
      (leftCfg a.tm b.tm (haltList a.tm
        ((BitEncoding.frame x++Computability.unaryEncodeNat n).map a.outputAlphabet.symm))) suffix from
      by rw [left_handoff]; exact hs)
  have hc := acceptingCount_of_iterate a.tm.step (M a b ha hb).view (leftCfg a.tm b.tm)
    (fun {c d} => left_view a b ha hb c d) (fuel:=suffix) prep.evals_in_steps
  rw [left_handoff,hsc] at hc
  rw [←initial_eq a b ha hb x] at hprep hc
  have hle : prep.steps+suffix ≤ aprep+3*x.length+4+3*n+vtime := by
    have hp := prep.steps_le_m
    simp only [suffix,BitEncoding.frame_length]
    omega
  exact ⟨hprep.mono hle, (hprep.acceptingCount_eq_of_le hle).trans
    (hc.trans (bitsWordCount_eq_card V n))⟩

end
end PlanarHom.CertificateGeneratorMachine
