import PlanarHom.FixedRealWordSumBounds
import PlanarHom.PartitionOutputBounds
import PlanarHom.FixedRealExtensionPresentation

/-! NEW Lemma A.1 output-size existence for original finite-language partition
functions over fixed finitely generated real-field presentations. Contributions
use one factor per vertex and occurrence, so all share both denominator layers.
The exponential coloring sum is not claimed to be computed in polynomial time. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealPartitionOutputBounds
open DensePolynomial FixedRealAlphabet FixedRealWordSums Complexity
variable {n e:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable {bt ut:ℕ}

 abbrev Factor := PartitionOutputBounds.Factor C bt ut
 def alphabet (M:Fin bt→Matrix C C K) (U:Fin ut→C→K) (w:C→K) :
    Fin (Fintype.card (Factor (C:=C) (bt:=bt) (ut:=ut)))→K :=
  fun a=>PartitionOutputBounds.factorValue M U w ((Fintype.equivFin _).symm a)

 def words (g:MixedCode) : List (List (Fin (Fintype.card (Factor (C:=C) (bt:=bt) (ut:=ut))))) :=
    (Finset.univ:Finset (Fin g.vertices→C)).toList.map (fun σ=>
      (PartitionOutputBounds.assignmentWord (binaryTypes:=bt) (unaryTypes:=ut) g σ).map (Fintype.equivFin _))

 def length (g:MixedCode) : ℕ := g.vertices+g.edges.length+g.unaries.length

 theorem words_length (g:MixedCode) :
    (words (C:=C) (bt:=bt) (ut:=ut) g).length=(Fintype.card C)^g.vertices := by
  simp [words,Fintype.card_fun]

 theorem word_length (g:MixedCode) (xs:List (Fin (Fintype.card (Factor (C:=C) (bt:=bt) (ut:=ut)))))
    (hx:xs∈words (C:=C) (bt:=bt) (ut:=ut) g) : xs.length=length g := by
  obtain ⟨σ,hσ,rfl⟩:=List.mem_map.mp hx
  rw [List.length_map,PartitionOutputBounds.assignmentWord_length]
  rfl

 theorem sum_words_eq (M:Fin bt→Matrix C C K) (U:Fin ut→C→K) (w:C→K)
    (g:MixedCode) (hg:g.Valid bt ut) :
    ((words (C:=C) (bt:=bt) (ut:=ut) g).map (fun xs=>(xs.map (alphabet M U w)).prod)).sum=
      g.evaluate hg M U w := by
  simp only [words,List.map_map,Function.comp_def,alphabet,Equiv.symm_apply_apply]
  rw [Finset.sum_map_toList]
  simp only [MixedCode.evaluate,PartitionOutputBounds.assignmentWord_product]

 def code (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (M:Fin bt→Matrix C C K) (U:Fin ut→C→K) (w:C→K) (g:MixedCode) : FixedRealExtension.Code n e :=
    sumWords (data basis (alphabet M U w)) (length g) (words (C:=C) (bt:=bt) (ut:=ut) g)

 theorem code_valid (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (M:Fin bt→Matrix C C K) (U:Fin ut→C→K) (w:C→K) (g:MixedCode) :
    FixedRealExtension.Valid n (code basis M U w g) := sumWords_valid _ _ _

 theorem code_value (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (M:Fin bt→Matrix C C K) (U:Fin ut→C→K) (w:C→K) (g:MixedCode) (hg:g.Valid bt ut) :
    FixedRealExtension.value basis (code basis M U w g)=g.evaluate hg M U w := by
  rw [code,sumWords_value _ _ _ (word_length g)]
  exact sum_words_eq M U w g hg

 theorem code_size (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (M:Fin bt→Matrix C C K) (U:Fin ut→C→K) (w:C→K) :
    ∃P:Polynomial ℕ,∀g:MixedCode,
      ((FixedRealExtension.encoding n e).encode (code basis M U w g)).length≤
        P.eval (MixedCode.encoding.encode g).length := by
  let Q:=max 1 (Fintype.card C)
  let d:=data basis (alphabet M U w)
  let P:=FixedRealWordSums.outputPolynomial (bounds d) Q
  refine ⟨P,?_⟩
  intro g
  have hc:(words (C:=C) (bt:=bt) (ut:=ut) g).length≤Q^(length g+1) := by
    rw [words_length]
    apply (Nat.pow_le_pow_left (Nat.le_max_right _ _) g.vertices).trans
    exact Nat.pow_le_pow_right (Nat.le_max_left 1 _) (by dsimp[length];omega)
  have hs:=sumWords_size d Q (length g) (Nat.le_max_left 1 _) _ (word_length g) hc
  exact hs.trans (MachineComposition.natPolynomial_monotone P (MixedCode.size_le_length g))

/-- Polynomial-size exact prescribed-presentation answer, without an evaluation
algorithm or an input-dependent arithmetic certificate. -/
 theorem exists_polynomial_partition_representation (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (M:Fin bt→Matrix C C K) (U:Fin ut→C→K) (w:C→K) :
    ∃P:Polynomial ℕ,∀g:MixedCode,∀hg:g.Valid bt ut,
      ∃c:FixedRealExtension.Code n e,FixedRealExtension.Valid n c ∧
        FixedRealExtension.value basis c=g.evaluate hg M U w ∧
          ((FixedRealExtension.encoding n e).encode c).length≤P.eval (MixedCode.encoding.encode g).length := by
  obtain ⟨P,hP⟩:=code_size basis M U w
  exact ⟨P,fun g hg=>⟨code basis M U w g,code_valid basis M U w g,code_value basis M U w g hg,hP g⟩⟩

end PlanarHom.FixedRealPartitionOutputBounds
