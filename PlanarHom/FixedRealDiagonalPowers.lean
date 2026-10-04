import PlanarHom.FixedRealPositiveWeightRemoval
import PlanarHom.RelativeRationalPowerField
import PlanarHom.FixedRealJointInterpolation
import PlanarHom.UnaryLoopRealization

/-! NEW finite joint rational diagonal/unary availability for A.8. The target
constants have their literal real powers; compatibility is derived from the
positive diagonal relation, and unary occurrences become actual loops. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealWeightRemoval
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open FixedRealMixedInterpolation ProductCompatibility FiniteLanguageAliases RelativeWeightedSpectralField
variable {n e q bt ut s:ℕ} {F:Type} [Field F] [Algebra (RationalFunction n) F] [Algebra F ℝ]
variable (basis:Module.Basis (Fin e) (RationalFunction n) F)

theorem diagonal_compatible (w v:Fin q→F) (hw:∀i,0<realWeights w i) (r:ℚ)
    (hv:∀i,realWeights v i=realWeights w i^(r:ℝ)) :
    Compatible (fun p:Fin q×Fin q=>Matrix.diagonal (fun i=>(w i)⁻¹) p.1 p.2)
      (fun p=>Matrix.diagonal v p.1 p.2) := by
  apply compatible_of_field_embedding (algebraMap F ℝ)
  have hsrc:(fun p:Fin q×Fin q=>algebraMap F ℝ (Matrix.diagonal (fun i=>(w i)⁻¹) p.1 p.2))=
      (fun p=>Matrix.diagonal (fun i=>(realWeights w i)⁻¹) p.1 p.2) := by
    funext p
    by_cases h:p.1=p.2 <;> simp [Matrix.diagonal_apply,realWeights,h]
  have htgt:(fun p:Fin q×Fin q=>algebraMap F ℝ (Matrix.diagonal v p.1 p.2))=
      (fun p=>PositiveWeightRemoval.diagonalPower (realWeights w) r p.1 p.2) := by
    funext p
    by_cases h:p.1=p.2 <;> simp [Matrix.diagonal_apply,realWeights,PositiveWeightRemoval.diagonalPower,h]
    exact hv p.2
  rw [hsrc,htgt]
  exact PositiveWeightRemoval.diagonalPower_compatible (realWeights w) hw r

theorem diagonal_zero (w v:Fin q→F) (hw:∀i,0<realWeights w i)
    (i j:Fin q) (hz:Matrix.diagonal (fun i=>(w i)⁻¹) i j=0) : Matrix.diagonal v i j=0 := by
  have hne:i≠j := by
    intro h
    subst j
    have hw0:w i≠0 := by
      intro h0
      exact (ne_of_gt (hw i)) (by simp [realWeights,h0])
    exact (inv_ne_zero hw0) (by simpa using hz)
  simp [Matrix.diagonal_apply,hne]

def diagonalUnaryAppendReduction (M:Fin bt→Matrix (Fin q) (Fin q) F)
    (U:Fin ut→Fin q→F) (w:Fin q→F) (selected:Fin bt) :
    Reduction (problem basis M (appendOne U (fun i=>M selected i i)) w) (problem basis M U w) := by
  apply queryReduction (presentation basis) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
    (PlanarValid bt (ut+1)) (PlanarValid bt ut)
    (totalEvaluation M (appendOne U (fun i=>M selected i i)) w) (totalEvaluation M U w)
    (realizeUnaryLoops ut selected.val) (fp_realizeUnaryLoops ut selected.val)
  · intro g hg
    exact realizeUnaryLoops_planar selected g hg
  · intro g hg
    rw [totalEvaluation_valid _ _ _ _ (realizeUnaryLoops_valid selected g hg.1),
      totalEvaluation_valid _ _ _ g hg.1]
    exact evaluate_realizeUnaryLoops selected g hg.1 M U w

def unaryDiagonalFamily (M:Fin bt→Matrix (Fin q) (Fin q) F)
    (U:Fin ut→Fin q→F) (w:Fin q→F) (selected:Fin s→Fin bt) :
    Reduction (problem basis M (appendFamily U (fun j i=>M (selected j) i i)) w)
      (problem basis M U w) := by
  induction s with
  | zero=>
    simpa only [appendFamily_zero] using queryReduction (presentation basis)
      MixedCode.encoding MixedCode.encoding MixedCode.normalizer (PlanarValid bt ut) (PlanarValid bt ut)
      (totalEvaluation M U w) (totalEvaluation M U w) id (fp_id MixedCode.encoding)
      (fun _ h=>h) (fun _ _=>rfl)
  | succ s ih=>
    have last:=diagonalUnaryAppendReduction basis M
      (appendFamily U (fun j:Fin s=>fun i=>M (selected j.castSucc) i i)) w (selected (Fin.last s))
    rw [appendFamily_succ]
    exact last.trans (ih (fun j=>selected j.castSucc))

/-- A fixed finite family of binary D^r labels, alongside every old binary and
unary type, reduces to the original weighted source. -/
def diagonalPowers_joint (M:Fin bt→Matrix (Fin q) (Fin q) F)
    (U:Fin ut→Fin q→F) (w:Fin q→F) (old:Fin bt)
    (hs:∀i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw:∀i,0<realWeights w i) (hnonzero:∀i,realMatrix (M old) i≠0)
    (hproj:∀i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j)
    (r:Fin s→ℚ) (v:Fin s→Fin q→F)
    (hv:∀j i,realWeights (v j) i=realWeights w i^(r j:ℝ)) :
    Reduction (problem basis (appendFamily (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹)))
      (fun j=>Matrix.diagonal (v j))) U w) (problem basis M U w) := by
  apply binaryFinite_joint basis (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹))) U w
    (fun j=>Matrix.diagonal (v j)) (fun _=>Fin.last bt)
    (fun j i k=>by simpa only [appendOne_aux] using diagonal_zero w (v j) hw i k)
    (fun j=>by
      simp only [appendOne_aux]
      exact hasProductMaps_of_compatible _ _ (diagonal_compatible w (v j) hw (r j) (hv j)))
    (problem basis M U w) (inverseDiagonalFromRows basis M U w old hs hw hnonzero hproj)

end PlanarHom.FixedRealWeightRemoval
