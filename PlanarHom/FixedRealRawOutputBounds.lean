import PlanarHom.FixedRealPartitionOutputBounds
import PlanarHom.GraphCodeNormalization

/-! NEW raw-word form of the output-size theorem. Successful noncanonical graph
words are charged at their literal input length through the proved normalizer. -/
noncomputable section
namespace PlanarHom.FixedRealPartitionOutputBounds
open DensePolynomial Complexity RepresentedBit
variable {n e:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable {bt ut:ℕ}

 theorem exists_polynomial_raw_answer_bound (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (M:Fin bt→Matrix C C K) (U:Fin ut→C→K) (w:C→K) :
    ∃P:Polynomial ℕ,∀raw:Bits,∀g:MixedCode,MixedCode.encoding.decode raw=some g→
      ∀hg:g.Valid bt ut,∃out:Bits,
        (FixedRealExtension.presentation basis).Represents out (g.evaluate hg M U w) ∧
          out.length≤P.eval raw.length := by
  obtain ⟨P,hP⟩:=code_size basis M U w
  let Q:=MachineComposition.outputLengthPolynomial MixedCode.normalizer
  refine ⟨P.comp Q,?_⟩
  intro raw g hd hg
  let input:BitEncoding.ValidWord MixedCode.encoding:=⟨raw,⟨g,hd⟩⟩
  have hi:input.value=g:=BitEncoding.ValidWord.value_eq hd
  have hl:=MachineComposition.encoded_output_length_le MixedCode.normalizer input
  change (MixedCode.encoding.encode input.value).length≤Q.eval raw.length at hl
  rw [hi] at hl
  let c:=code basis M U w g
  refine ⟨(FixedRealExtension.encoding n e).encode c,?_,?_⟩
  · exact ⟨c,(FixedRealExtension.encoding n e).decode_encode c,code_valid basis M U w g,code_value basis M U w g hg⟩
  · have hh:((FixedRealExtension.encoding n e).encode c).length≤P.eval (Q.eval raw.length):=
      (hP g).trans (MachineComposition.natPolynomial_monotone P hl)
    simpa only [Polynomial.eval_comp] using hh

 theorem empty_graph_value (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (M:Fin bt→Matrix C C K) (U:Fin ut→C→K) (w:C→K) :
    FixedRealExtension.value basis (code basis M U w ⟨0,[],[]⟩)=1 := by
  rw [code_value basis M U w _ (show MixedCode.Valid bt ut ⟨0,[],[]⟩ from ⟨by simp,by simp⟩)]
  simp [MixedCode.evaluate]

 theorem no_colors_value [IsEmpty C] (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (M:Fin bt→Matrix C C K) (U:Fin ut→C→K) (w:C→K) (g:MixedCode) (hg:g.Valid bt ut)
    (h:0<g.vertices) : FixedRealExtension.value basis (code basis M U w g)=0 := by
  letI : IsEmpty (Fin g.vertices→C):=⟨fun f=>isEmptyElim (f ⟨0,h⟩)⟩
  rw [code_value basis M U w g hg]
  simp [MixedCode.evaluate]

end PlanarHom.FixedRealPartitionOutputBounds

namespace PlanarHom.FixedRealWordSums
open DensePolynomial FixedRealAlphabet
variable {n e t:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable {basis:Module.Basis (Fin e) (RationalFunction n) K} {A:Fin t→K}

 theorem sumWords_nil_value (d:Data basis A) (L:ℕ) : FixedRealExtension.value basis (sumWords d L [])=0 := by
  simpa using sumWords_value d L [] (by simp)

 theorem sumWords_empty_word_value (d:Data basis A) : FixedRealExtension.value basis (sumWords d 0 [[]])=1 := by
  simpa using sumWords_value d 0 [[]] (by simp)

 theorem zero_factor_word_value (d:Data basis A) (xs:List (Fin t))
    (h:∃a∈xs,A a=0) : FixedRealExtension.value basis (word d xs)=0 := by
  rw [word_value]
  obtain ⟨a,ha,hz⟩:=h
  apply List.prod_eq_zero
  exact List.mem_map.mpr ⟨a,ha,hz⟩

 theorem empty_alphabet_word (xs:List (Fin 0)) : xs=[] := by
  cases xs with
  | nil=>rfl
  | cons a xs=>exact Fin.elim0 a

 theorem empty_alphabet_sum (A:Fin 0→K) (d:Data basis A) (words:List (List (Fin 0))) :
    FixedRealExtension.value basis (sumWords d 0 words)=(words.length:K) := by
  rw [sumWords_value d 0 words (fun xs _=>by rw [empty_alphabet_word xs];rfl)]
  have he:∀xs:List (Fin 0),(xs.map A).prod=1:=by intro xs;rw [empty_alphabet_word xs];rfl
  simp only [he,List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one]

end PlanarHom.FixedRealWordSums
