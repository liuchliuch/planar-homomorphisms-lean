import PlanarHom.GraphCodeNormalization
import PlanarHom.RationalNormalizationMachine
import PlanarHom.ArithmeticCircuitPrimitives

/-! Actual normalization of raw rational and fixed-coordinate codes. This is
only lexical/rational coefficient normalization, never a multivariate fraction
gcd or a choice of canonical representative of a transcendental field value. -/
noncomputable section
open Classical
namespace PlanarHom.Complexity.BitEncoding
open Turing PlanarHom.MachineComposition ArithmeticCircuitPrimitives

private theorem bool_roundtrip {s:Bits} {b:Bool} (h:bool.decode s=some b) : bool.encode b=s := by
  cases s with
  | nil => simp [bool] at h
  | cons a xs =>
    cases xs with
    | nil => simp [bool] at h; subst b; rfl
    | cons c xs => simp [bool] at h

def boolNormalizer : Normalizer bool := by
  apply Classical.choice
  exact fp_code_view (ValidWord.encoding bool) bool ValidWord.value
    (fun w=>bool_roundtrip w.decode_raw)

def intNormalizer : Normalizer int := by
  apply retractNormalizer (bool.prod nat)
    (fun z:ℤ=>match z with | .ofNat n=>(false,n) | .negSucc n=>(true,n))
    (fun p=>if p.1 then Int.negSucc p.2 else Int.ofNat p.2)
    (by intro z; cases z <;> rfl)
    (by rintro ⟨b,n⟩; cases b <;> rfl)
    (prodNormalizer boolNormalizer natNormalizer)

def ratNormalizer : Normalizer rat := by
  let e:=int.prod nat
  let f:=fun q:ℚ=>(q.num,q.den)
  let g:=fun p:ℤ×ℕ=>mkRat p.1 p.2
  let view:=retractWord e f g Rat.mkRat_self
  have hv:FP (ValidWord.encoding rat) (ValidWord.encoding e) view:=
    fp_code_view _ _ _ (fun _=>rfl)
  have hn:=hv.comp ⟨prodNormalizer intNormalizer natNormalizer⟩
  have h:=hn.comp BinaryArithmetic.fp_rational_normalization
  apply Classical.choice
  exact h.congr (fun w=>(retractWord_value e f g Rat.mkRat_self w).symm)

private def vectorWord {A:Type} (e:BitEncoding A) (n:ℕ) (w:ValidWord (e.vector n)) : ValidWord e.list := by
  refine ⟨w.raw,?_⟩
  obtain ⟨v,hv⟩:=w.property
  change (e.vector n).decode w.raw=some v at hv
  cases h:e.list.decode w.raw with
  | none => simp only [vector,h,Option.bind_eq_bind,Option.bind_none,reduceCtorEq] at hv
  | some xs => exact ⟨xs,rfl⟩

private theorem vectorWord_value {A:Type} (e:BitEncoding A) (n:ℕ) (w:ValidWord (e.vector n)) :
    (vectorWord e n w).value=List.ofFn w.value := by
  have hd:=w.decode_raw
  have hl: e.list.decode w.raw=some (vectorWord e n w).value := (vectorWord e n w).decode_raw
  change (e.vector n).decode w.raw=some w.value at hd
  simp only [vector,hl,Option.bind_eq_bind,Option.bind_some] at hd
  split_ifs at hd with hlen
  · have he:=Option.some.inj hd
    rw [←he]
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using hlen
    · intro i hi hj
      simp only [List.getElem_ofFn]

/-- A length-checked vector needs no normalization beyond its recursively
normalized coefficient list; rebuilding the vector has identical output bits. -/
def vectorNormalizer {A:Type} {e:BitEncoding A} (h:Normalizer e) (n:ℕ) : Normalizer (e.vector n) := by
  have hv:FP (ValidWord.encoding (e.vector n)) (ValidWord.encoding e.list) (vectorWord e n):=
    fp_code_view _ _ _ (fun _=>rfl)
  have hn:=hv.comp ⟨listNormalizer h⟩
  apply Classical.choice
  apply hn.transportOutput
  intro w
  change e.list.encode (vectorWord e n w).value=e.list.encode (List.ofFn w.value)
  rw [vectorWord_value]

def numberFieldNormalizer {K:Type} [Field K] [Algebra ℚ K] {n:ℕ}
    (basis:Module.Basis (Fin n) ℚ K) : Normalizer (numberFieldEncoding basis) :=
  retractNormalizer (rationalCoordinates n) basis.equivFun basis.equivFun.symm
    basis.equivFun.symm_apply_apply basis.equivFun.apply_symm_apply (vectorNormalizer ratNormalizer n)

end PlanarHom.Complexity.BitEncoding
