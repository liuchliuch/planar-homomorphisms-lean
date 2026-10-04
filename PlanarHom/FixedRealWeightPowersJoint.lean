import PlanarHom.FixedRealDiagonalPowers

/-! NEW simultaneous rational diagonal and unary language. The inverse diagonal
is retained too, so the very same language can use unit background via actual
loops. No old binary or unary label is dropped. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealWeightRemoval
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open FixedRealMixedInterpolation FiniteLanguageAliases RelativeWeightedSpectralField
variable {n e q bt ut s:ℕ} {F:Type} [Field F] [Algebra (RationalFunction n) F] [Algebra F ℝ]
variable (basis:Module.Basis (Fin e) (RationalFunction n) F)

def powerMatrices (M:Fin bt→Matrix (Fin q) (Fin q) F) (w:Fin q→F) (v:Fin s→Fin q→F) :=
  appendFamily (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹))) (fun j=>Matrix.diagonal (v j))
def powerUnaries (U:Fin ut→Fin q→F) (v:Fin s→Fin q→F) := appendFamily U v

def powersUnary_joint (M:Fin bt→Matrix (Fin q) (Fin q) F)
    (U:Fin ut→Fin q→F) (w:Fin q→F) (old:Fin bt)
    (hs:∀i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw:∀i,0<realWeights w i) (hnonzero:∀i,realMatrix (M old) i≠0)
    (hproj:∀i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j)
    (r:Fin s→ℚ) (v:Fin s→Fin q→F)
    (hv:∀j i,realWeights (v j) i=realWeights w i^(r j:ℝ)) :
    Reduction (problem basis (powerMatrices M w v) (powerUnaries U v) w) (problem basis M U w) := by
  have hu:=unaryDiagonalFamily basis (powerMatrices M w v) U w (Fin.natAdd (bt+1):Fin s→Fin (bt+1+s))
  have he:(fun j i=>powerMatrices M w v (Fin.natAdd (bt+1) j) i i)=v := by
    funext j i
    simp only [powerMatrices,appendFamily_new,Matrix.diagonal_apply_eq]
  rw [he] at hu
  exact hu.trans (diagonalPowers_joint basis M U w old hs hw hnonzero hproj r v hv)

def powersUnary_unit_joint (M:Fin bt→Matrix (Fin q) (Fin q) F)
    (U:Fin ut→Fin q→F) (w:Fin q→F) (old:Fin bt)
    (hs:∀i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw:∀i,0<realWeights w i) (hnonzero:∀i,realMatrix (M old) i≠0)
    (hproj:∀i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j)
    (r:Fin s→ℚ) (v:Fin s→Fin q→F)
    (hv:∀j i,realWeights (v j) i=realWeights w i^(r j:ℝ)) :
    Reduction (problem basis (powerMatrices M w v) (powerUnaries U v) (fun _=>1)) (problem basis M U w) := by
  have hc:∀i,w i*powerMatrices M w v (Fin.castAdd s (Fin.last bt)) i i=1 := by
    intro i
    simp only [powerMatrices,appendFamily_old,appendOne_aux,Matrix.diagonal_apply_eq]
    apply mul_inv_cancel₀
    intro hz
    exact (ne_of_gt (hw i)) (by simp [realWeights,hz])
  exact (FixedRealWeightedGadgets.loopCancellationReduction basis (powerMatrices M w v) (powerUnaries U v) w
    (Fin.castAdd s (Fin.last bt)) hc).trans (powersUnary_joint basis M U w old hs hw hnonzero hproj r v hv)

end PlanarHom.FixedRealWeightRemoval
