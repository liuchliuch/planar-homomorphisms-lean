import PlanarHom.ZeroOneMixedVerifier

/-! NEW genuine #P membership on the original raw mixed-code interface. -/
noncomputable section
open Classical
namespace PlanarHom.ZeroOneMixedMembership
open Complexity ZeroOneSharpPMembership

def totalCount (q:ℕ) (R:Relation q) (raw:Bits) : ℕ :=
  match MixedCode.encoding.decode raw with
  | none=>0
  | some g=>if hg:g.Valid 1 0 then ZeroOneSharpPMembership.count q R g.underlying (g.underlying_valid hg) else 0

def witnessPolynomial (q:ℕ) : Polynomial ℕ := (Polynomial.C 49*(Polynomial.X+1))*Polynomial.C q

theorem parser_of_decode (raw:Bits) (g:MixedCode) (hd:MixedCode.encoding.decode raw=some g) :
    MixedCode.totalParser.run raw=(true,g) := by
  have hs:=MixedCode.totalParser_correct raw
  rw [hd] at hs
  cases hb:(MixedCode.totalParser.run raw).1
  · simp [hb] at hs
  · have hv:(MixedCode.totalParser.run raw).2=g := by simpa [hb] using hs.symm
    exact Prod.ext hb hv

theorem totalCount_decode (q:ℕ) (R:Relation q) (raw:Bits) (g:MixedCode)
    (hd:MixedCode.encoding.decode raw=some g) (hg:g.Valid 1 0) :
    totalCount q R raw=ZeroOneSharpPMembership.count q R g.underlying (g.underlying_valid hg) := by
  simp [totalCount,hd,hg]

theorem totalCount_certificate (q:ℕ) (R:Relation q) (raw:Bits) :
    totalCount q R raw=certificateCount (witnessPolynomial q) (verifier q R) raw := by
  cases hd:MixedCode.encoding.decode raw with
  | none =>
    have hp:(MixedCode.totalParser.run raw).1=false := by
      have h:=MixedCode.totalParser_correct raw
      rw [hd] at h
      cases hb:(MixedCode.totalParser.run raw).1
      · rfl
      · simp only [hb,ite_true] at h
        cases h
    simp [totalCount,hd,certificateCount,verifier,hp]
  | some g =>
    have hp:=parser_of_decode raw g hd
    by_cases hg:g.Valid 1 0
    · have hb:g.underlying.vertices≤49*(raw.length+1) := by
        have h:=MixedCode.raw_size_le raw g hd
        change g.vertices≤_
        omega
      have hcard:=certificate_card q R g.underlying (g.underlying_valid hg) (49*(raw.length+1)) hb
      rw [certificateCount_eq_card _ _ raw (49*(raw.length+1)*q) (by
        simp only [witnessPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,
          Polynomial.eval_X,Polynomial.eval_one])]
      simpa only [totalCount,hd,dif_pos hg,verifier,hp,hg,decide_true,Bool.true_and,Certificate] using hcard.symm
    · simp [totalCount,hd,hg,certificateCount,verifier,hp]

theorem totalCount_certificateSharpP (q:ℕ) (R:Relation q) : CertificateSharpP (totalCount q R) :=
  ⟨witnessPolynomial q,verifier q R,fp_verifier q R,totalCount_certificate q R⟩

theorem totalCount_sharpP (q:ℕ) (R:Relation q) : SharpP (totalCount q R) :=
  (totalCount_certificateSharpP q R).sharpP
end PlanarHom.ZeroOneMixedMembership
