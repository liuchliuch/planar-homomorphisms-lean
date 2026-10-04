import PlanarHom.FixedRealInverseDiagonal

/-! NEW A.8 retained-language positive weight removal for arbitrary represented
real constants. Actual Gram gadgets, weighted path interpolation and one inverse
loop at every vertex compose; isolated vertices and all mixed labels survive. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealWeightRemoval
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open FixedRealMixedInterpolation FiniteLanguageAliases RelativeWeightedSpectralField
open PositiveWeightRemoval (gramCoreField gramCore gramCore_posDef)
variable {n e q bt ut:ℕ} {F:Type} [Field F] [Algebra (RationalFunction n) F] [Algebra F ℝ]
variable (basis:Module.Basis (Fin e) (RationalFunction n) F)

theorem gramCoreField_real (A:Matrix (Fin q) (Fin q) F) (w:Fin q→F) :
    realMatrix (gramCoreField A w (max 1 (q-1)))=gramCore (realMatrix A) (realWeights w) := by
  have hd:(algebraMap F ℝ).mapMatrix (Matrix.diagonal w)=Matrix.diagonal (realWeights w) := by
    ext i j
    by_cases h:i=j <;> simp [Matrix.diagonal_apply,realWeights,h]
  have hm:(A*Matrix.diagonal w*A).map (algebraMap F ℝ)=
      realMatrix A*Matrix.diagonal (realWeights w)*realMatrix A := by
    change (algebraMap F ℝ).mapMatrix (A*Matrix.diagonal w*A)=_
    rw [map_mul,map_mul,hd]
    rfl
  apply Matrix.ext
  intro i j
  change algebraMap F ℝ (((A*Matrix.diagonal w*A) i j)^max 1 (q-1))=_
  rw [map_pow]
  change ((A*Matrix.diagonal w*A).map (algebraMap F ℝ) i j)^max 1 (q-1)=_
  rw [hm]
  rfl

def inverseDiagonalFromRows (M:Fin bt→Matrix (Fin q) (Fin q) F)
    (U:Fin ut→Fin q→F) (w:Fin q→F) (old:Fin bt)
    (hs:∀i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw:∀i,0<realWeights w i) (hnonzero:∀i,realMatrix (M old) i≠0)
    (hproj:∀i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j) :
    Reduction (problem basis (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹))) U w)
      (problem basis M U w) := by
  let G:=gramCoreField (M old) w (max 1 (q-1))
  have hG:(realMatrix G).PosDef := by
    rw [show realMatrix G=gramCore (realMatrix (M old)) (realWeights w) from gramCoreField_real _ _]
    exact gramCore_posDef _ hs _ hw hnonzero hproj
  let hgram:=FixedRealWeightedGadgets.gramAppendReduction basis M U w old (max 1 (q-1))
  have haux:(realMatrix (appendOne M G (Fin.last bt))).PosDef := by
    simpa only [appendOne_aux] using hG
  let hinv:=inverseDiagonalAppendReduction basis (appendOne M G) U w (Fin.last bt) haux hw
  exact (FixedRealWeightedGadgets.skipMiddleReduction basis M G (Matrix.diagonal (fun i=>(w i)⁻¹)) U w).trans
    (hinv.trans hgram)

def removePositiveWeights (M:Fin bt→Matrix (Fin q) (Fin q) F)
    (U:Fin ut→Fin q→F) (w:Fin q→F) (old:Fin bt)
    (hs:∀i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw:∀i,0<realWeights w i) (hnonzero:∀i,realMatrix (M old) i≠0)
    (hproj:∀i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j) :
    Reduction (problem basis M U (fun _=>1)) (problem basis M U w) := by
  let D:=Matrix.diagonal (fun i=>(w i)⁻¹)
  have he:(appendOne M D)∘Fin.castAdd 1=M := by
    funext l
    exact appendOne_old M D l
  have first:Reduction (problem basis M U (fun _=>1)) (problem basis (appendOne M D) U (fun _=>1)) := by
    simpa only [he] using FixedRealMixedInterpolation.binaryRelabelReduction basis (Fin.castAdd 1) (appendOne M D) U (fun _=>1)
  have hcancel:∀i,w i*appendOne M D (Fin.last bt) i i=1 := by
    intro i
    simp only [appendOne_aux,D,Matrix.diagonal_apply_eq]
    apply mul_inv_cancel₀
    intro h
    have hr:=congrArg (algebraMap F ℝ) h
    exact (ne_of_gt (hw i)) (by simpa only [map_zero] using hr)
  exact first.trans ((FixedRealWeightedGadgets.loopCancellationReduction basis (appendOne M D) U w (Fin.last bt) hcancel).trans
    (inverseDiagonalFromRows basis M U w old hs hw hnonzero hproj))

end PlanarHom.FixedRealWeightRemoval
