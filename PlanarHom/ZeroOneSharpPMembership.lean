import PlanarHom.ZeroOneVerifierMachines
import PlanarHom.ZeroOneCertificateBijection

/-! NEW genuine accepting-path #P membership for every fixed finite Boolean
homomorphism relation on ordinary raw graph words. Malformed words and invalid
endpoints have count zero; planarity is only a final promise restriction. -/
noncomputable section
open Classical
namespace PlanarHom.ZeroOneSharpPMembership
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

def totalCount (q:ℕ) (R:Relation q) (raw:Bits) : ℕ :=
  match GraphCode.encoding.decode raw with
  | none=>0
  | some g=>if hg:g.Valid then count q R g hg else 0

def verifier (q:ℕ) (R:Relation q) (p:Bits×Bits) : Bool :=
  let g:=GraphCode.totalParser.run p.1
  g.1 && verifyGraph q R g.2 p.2

def witnessPolynomial (q:ℕ) : Polynomial ℕ := (Polynomial.C 14*(Polynomial.X+1))*Polynomial.C q

theorem fp_verifier (q:ℕ) (R:Relation q) :
    FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool (verifier q R) := by
  have hraw:=fp_fst BitEncoding.bits BitEncoding.bits
  have hw:=fp_snd BitEncoding.bits BitEncoding.bits
  have hp:=hraw.comp GraphCode.fp_totalParser
  have hflag:=hp.comp (fp_fst BitEncoding.bool GraphCode.encoding)
  have hg:=hp.comp (fp_snd BitEncoding.bool GraphCode.encoding)
  exact (hflag.pair ((hg.pair hw).comp (fp_verifyGraph q R))).comp (fp_bool_gate (fun p=>p.1 && p.2))

theorem totalCount_decode (q:ℕ) (R:Relation q) (raw:Bits) (g:GraphCode)
    (hd:GraphCode.encoding.decode raw=some g) (hg:g.Valid) : totalCount q R raw=count q R g hg := by
  simp [totalCount,hd,hg]

theorem parser_of_decode (raw:Bits) (g:GraphCode) (hd:GraphCode.encoding.decode raw=some g) :
    GraphCode.totalParser.run raw=(true,g) := by
  have hs:=GraphCode.totalParser_correct raw
  rw [hd] at hs
  cases hb:(GraphCode.totalParser.run raw).1
  · simp [hb] at hs
  · have hv:(GraphCode.totalParser.run raw).2=g := by simpa [hb] using hs.symm
    exact Prod.ext hb hv

theorem certificateCount_eq_card (p:Polynomial ℕ) (V:Bits×Bits→Bool) (raw:Bits) (N:ℕ)
    (h:p.eval raw.length=N) : certificateCount p V raw=
      Fintype.card {w:Fin N→Bool // V (raw,List.ofFn w)=true} := by
  subst N
  rfl

theorem totalCount_certificate (q:ℕ) (R:Relation q) (raw:Bits) :
    totalCount q R raw=certificateCount (witnessPolynomial q) (verifier q R) raw := by
  cases hd:GraphCode.encoding.decode raw with
  | none =>
    have hp:(GraphCode.totalParser.run raw).1=false := by
      have h:=GraphCode.totalParser_correct raw
      rw [hd] at h
      cases hb:(GraphCode.totalParser.run raw).1
      · rfl
      · simp only [hb,ite_true] at h
        cases h
    simp [totalCount,hd,certificateCount,verifier,hp]
  | some g =>
    have hp:=parser_of_decode raw g hd
    by_cases hg:g.Valid
    · have hb:g.vertices≤14*(raw.length+1) := by have h:=GraphCode.raw_size_le raw g hd; omega
      have hcard:=certificate_card q R g hg (14*(raw.length+1)) hb
      rw [certificateCount_eq_card _ _ raw (14*(raw.length+1)*q) (by
        simp only [witnessPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,
          Polynomial.eval_X,Polynomial.eval_one])]
      simpa only [totalCount,hd,dif_pos hg,verifier,hp,Bool.true_and,Certificate] using hcard.symm
    · simp [totalCount,hd,hg,certificateCount,verifier,hp,verifyGraph]

theorem totalCount_certificateSharpP (q:ℕ) (R:Relation q) : CertificateSharpP (totalCount q R) :=
  ⟨witnessPolynomial q,verifier q R,fp_verifier q R,totalCount_certificate q R⟩

theorem totalCount_sharpP (q:ℕ) (R:Relation q) : SharpP (totalCount q R) :=
  (totalCount_certificateSharpP q R).sharpP

def planarProblem (q:ℕ) (R:Relation q) : PromiseProblem :=
  ⟨GraphCode.PlanarInput,fun raw=>BitEncoding.nat.encode (totalCount q R raw)⟩

theorem planar_membership (q:ℕ) (R:Relation q) :
    ∃f:Bits→ℕ,SharpP f ∧ ∀raw,(planarProblem q R).valid raw →
      (planarProblem q R).value raw=BitEncoding.nat.encode (f raw) :=
  ⟨totalCount q R,totalCount_sharpP q R,fun _ _=>rfl⟩
end PlanarHom.ZeroOneSharpPMembership
