import PlanarHom.FixedRealAlphabetMachines
import PlanarHom.FixedRealExtensionPresentation

/-! Public fixed-alphabet product endpoints. Valid natural-index words use
literally their original list code; no alphabet-checking or field-normalization
oracle is introduced by the semantic input restriction. -/
noncomputable section
namespace PlanarHom.FixedRealAlphabet
open DensePolynomial Complexity ArithmeticCircuitPrimitives
variable {n e t:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable {basis:Module.Basis (Fin e) (RationalFunction n) K} {A:Fin t→K}

def ValidNatWord (t:ℕ) (xs:List ℕ) : Prop := ∀a∈xs,a<t

def finiteWord (xs:{xs:List ℕ // ValidNatWord t xs}) : List (Fin t) :=
  xs.val.attach.map (fun a=>⟨a.val,xs.property a.val a.property⟩)

@[simp] theorem finiteWord_val (xs:{xs:List ℕ // ValidNatWord t xs}) :
    (finiteWord xs).map Fin.val=xs.val := by simp [finiteWord,List.map_map,Function.comp_def]

theorem finiteWord_code (xs:{xs:List ℕ // ValidNatWord t xs}) :
    (symbolEncoding t).list.encode (finiteWord xs)=BitEncoding.nat.list.encode xs.val := by
  have h:=congrArg (BitEncoding.nat.list.encode) (finiteWord_val xs)
  simpa only [BitEncoding.list,List.length_map,List.map_map,symbolEncoding,Function.comp_def] using h

def natWord (d:Data basis A) (xs:{xs:List ℕ // ValidNatWord t xs}) : FixedRealExtension.Code n e :=
  word d (finiteWord xs)

theorem fp_natWord (d:Data basis A) :
    FP (BitEncoding.nat.list.restrict (ValidNatWord t)) (FixedRealExtension.encoding n e) (natWord d) :=
  (fp_word d).transportInput finiteWord (fun xs=>finiteWord_code xs)

def natSymbol (A:Fin t→K) (a:ℕ) : K := if h:a<t then A ⟨a,h⟩ else 1

theorem natWord_value (d:Data basis A) (xs:{xs:List ℕ // ValidNatWord t xs}) :
    FixedRealExtension.value basis (natWord d xs)=(xs.val.map (natSymbol A)).prod := by
  rw [natWord,word_value,←finiteWord_val xs,List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  simp [Function.comp_def,natSymbol,a.isLt]

theorem natWord_valid (d:Data basis A) (xs:{xs:List ℕ // ValidNatWord t xs}) :
    FixedRealExtension.Valid n (natWord d xs) := word_valid d _

theorem natWord_size (d:Data basis A) (xs:{xs:List ℕ // ValidNatWord t xs}) :
    ((FixedRealExtension.encoding n e).encode (natWord d xs)).length≤
      (sizePolynomial (bounds d)).eval xs.val.length := by
  have hl:=congrArg List.length (finiteWord_val xs)
  simp only [List.length_map] at hl
  simpa only [natWord,hl] using word_size d (finiteWord xs)

private def symbolWord (w:BitEncoding.ValidWord (symbolEncoding t)) : BitEncoding.ValidWord BitEncoding.nat := by
  refine ⟨w.raw,?_⟩
  obtain ⟨a,ha⟩:=w.property
  cases h:BitEncoding.nat.decode w.raw with
  | none =>
    change (symbolEncoding t).decode w.raw=some a at ha
    simp only [symbolEncoding,h,Option.bind_eq_bind,Option.bind_none,reduceCtorEq] at ha
  | some a => exact ⟨a,rfl⟩

private theorem symbolWord_value (w:BitEncoding.ValidWord (symbolEncoding t)) :
    (symbolWord w).value=w.value.val := by
  have hd:=w.decode_raw
  have hn:BitEncoding.nat.decode w.raw=some (symbolWord w).value := (symbolWord w).decode_raw
  change (symbolEncoding t).decode w.raw=some w.value at hd
  simp only [symbolEncoding,hn,Option.bind_eq_bind,Option.bind_some] at hd
  split_ifs at hd with h
  · exact congrArg Fin.val (Option.some.inj hd)

def symbolNormalizer (t:ℕ) : BitEncoding.Normalizer (symbolEncoding t) := by
  have hv:FP (BitEncoding.ValidWord.encoding (symbolEncoding t))
      (BitEncoding.ValidWord.encoding BitEncoding.nat) symbolWord :=
    fp_code_view _ _ _ (fun _=>rfl)
  have hn:=hv.comp ⟨BitEncoding.natNormalizer⟩
  apply Classical.choice
  apply hn.transportOutput
  intro w
  change BitEncoding.nat.encode (symbolWord w).value=BitEncoding.nat.encode w.value.val
  rw [symbolWord_value]

/-- Every raw lexical input word decoded by the finite alphabet list codec is
admitted. Outputs are in the prescribed extension presentation. -/
theorem product_inFP (basis:Module.Basis (Fin e) (RationalFunction n) K) (A:Fin t→K) :
    ((FixedRealExtension.presentation basis).problem (symbolEncoding t).list
      (fun _=>True) (fun xs=>(xs.map A).prod)).InFP :=
  RepresentedBit.Presentation.problem_inFP _ _ (BitEncoding.listNormalizer (symbolNormalizer t))
    _ _ (word (data basis A)) (fp_word _) (fun xs _=>word_valid _ xs) (fun xs _=>word_value _ xs)

end PlanarHom.FixedRealAlphabet
