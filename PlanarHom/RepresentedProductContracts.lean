import PlanarHom.RepresentedExponentWords
import PlanarHom.RepresentedFixedLinearArithmetic
import PlanarHom.FixedRealExtensionEquality

/-! Exact operational contracts consumed by the represented interpolation
compiler. Equality is instantiated for the actual fixed-extension codes.
The word-product capability is kept explicit until its independent degree and
height proof is supplied; it is not inferred from primitive multiplication. -/
noncomputable section
open Classical
namespace PlanarHom.RepresentedBit
open Complexity
variable {K:Type} [CommSemiring K]

structure EqualityMachine (P:Presentation K) where
  test : P.Code×P.Code→Bool
  fp : FP (P.encoding.prod P.encoding) BitEncoding.bool test
  correct : ∀a b,P.valid a→P.valid b→(test (a,b)=true ↔ P.value a=P.value b)

abbrev ValidCode (P:Presentation K) := {c:P.Code//P.valid c}
def validEncoding (P:Presentation K) : BitEncoding (ValidCode P) := P.encoding.restrict P.valid
def validValue (P:Presentation K) (c:ValidCode P) : K := P.value c.val

def EqualityMachine.validTest {P:Presentation K} (M:EqualityMachine P) (p:ValidCode P×ValidCode P) : Bool :=
  M.test (p.1.val,p.2.val)

theorem EqualityMachine.fp_validTest {P:Presentation K} (M:EqualityMachine P) :
    FP ((validEncoding P).prod (validEncoding P)) BitEncoding.bool M.validTest := by
  have hc:FP ((validEncoding P).prod (validEncoding P)) (P.encoding.prod P.encoding)
      (fun p=>(p.1.val,p.2.val)):=fp_code_view _ _ _ (fun _=>rfl)
  exact hc.comp M.fp

theorem EqualityMachine.validTest_eq {P:Presentation K} (M:EqualityMachine P) (a b:ValidCode P) :
    M.validTest (a,b)=decide (validValue P a=validValue P b) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using M.correct a.val b.val a.property b.property

def properWord (t:ℕ) (w:List ℕ) : Prop := ∀i∈w,i<t
def wordEncoding (t:ℕ) : BitEncoding {w:List ℕ//properWord t w} := BitEncoding.nat.list.restrict (properWord t)

structure WordProductMachine (P:Presentation K) {t:ℕ} (A:Fin t→K) where
  run : {w:List ℕ//properWord t w}→P.Code
  fp : FP (wordEncoding t) P.encoding run
  valid : ∀w,P.valid (run w)
  value : ∀w,P.value (run w)=(w.val.map (RepresentedExponentWords.symbol A)).prod

def clippedWord {t:ℕ} (p:ℕ×(Fin t→ℕ)) : {w:List ℕ//properWord t w} :=
  ⟨RepresentedExponentWords.word p.1 p.2,fun i hi=>RepresentedExponentWords.mem_word_bound hi⟩

theorem fp_clippedWord (t:ℕ) : FP (RepresentedExponentWords.inputEncoding t) (wordEncoding t) clippedWord :=
  (RepresentedExponentWords.fp_word t).transportOutput (fun _=>rfl)

def WordProductMachine.clipped {P:Presentation K} {t:ℕ} {A:Fin t→K} (M:WordProductMachine P A)
    (p:ℕ×(Fin t→ℕ)) : ValidCode P := ⟨M.run (clippedWord p),M.valid _⟩

theorem WordProductMachine.fp_clipped {P:Presentation K} {t:ℕ} {A:Fin t→K} (M:WordProductMachine P A) :
    FP (RepresentedExponentWords.inputEncoding t) (validEncoding P) M.clipped :=
  ((fp_clippedWord t).comp M.fp).transportOutput (fun _=>rfl)

theorem WordProductMachine.clipped_value {P:Presentation K} {t m:ℕ} {A:Fin t→K}
    (M:WordProductMachine P A) {r:Fin t→ℕ} (hr:r∈ExponentProductTables.vectors t m) :
    validValue P (M.clipped (m,r))=∏i,A i^(r i) := by
  rw [validValue,WordProductMachine.clipped,M.value]
  exact RepresentedExponentWords.word_product_of_vector A hr

end PlanarHom.RepresentedBit
namespace PlanarHom.FixedRealRootRestriction
open DensePolynomial RepresentedBit
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

def equalityMachine (basis:Module.Basis (Fin e) (RationalFunction n) K) :
    EqualityMachine (FixedRealExtension.presentation basis) where
  test:=FixedRealExtension.equality n e
  fp:=FixedRealExtension.fp_equality n e
  correct:=FixedRealExtension.equality_value_iff basis

end PlanarHom.FixedRealRootRestriction
