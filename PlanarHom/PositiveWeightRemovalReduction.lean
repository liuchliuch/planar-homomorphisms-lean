import PlanarHom.InverseDiagonalAvailability
import PlanarHom.WeightedGramAvailability
import PlanarHom.LoopCancellationReduction
import PlanarHom.MixedLabelAliasReductions

/-! The literal weighted Gram gadget, weighted spectral interpolation, and one
inverse-diagonal loop at every vertex compose into actual weight removal. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.PositiveWeightRemoval
open Complexity Complexity.MixedCode FiniteLanguageAliases SpectralFieldPresentation
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q bt ut dimension : ℕ}

theorem gramCoreField_real (A : Matrix (Fin q) (Fin q) K₀) (w : Fin q → K₀) :
    realMatrix (gramCoreField A w (max 1 (q-1))) = gramCore (realMatrix A) (realWeights w) := by
  have hd : K₀.val.toRingHom.mapMatrix (Matrix.diagonal w)=Matrix.diagonal (realWeights w) := by
    ext i j
    by_cases h : i=j <;> simp [Matrix.diagonal_apply,realWeights,h]
  have hm : (A*Matrix.diagonal w*A).map K₀.val =
      realMatrix A*Matrix.diagonal (realWeights w)*realMatrix A := by
    change K₀.val.toRingHom.mapMatrix (A*Matrix.diagonal w*A)=_
    rw [map_mul,map_mul,hd]
    rfl
  apply Matrix.ext
  intro i j
  change K₀.val (((A*Matrix.diagonal w*A) i j)^max 1 (q-1))=_
  rw [map_pow]
  change ((A*Matrix.diagonal w*A).map K₀.val i j)^max 1 (q-1)=_
  rw [hm]
  rfl

/-- Adding a temporary matrix before a retained final matrix is a genuine
finite-label query reduction; no constraint is silently identified. -/
def skipMiddleReduction (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (N P : Matrix (Fin q) (Fin q) K₀)
    (U : Fin ut → Fin q → K₀) (w : Fin q → K₀) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (appendOne M P) U w)
      (evaluationProblem basis (appendOne (appendOne M N) P) U w) := by
  let ρ : Fin (bt+1) → Fin (bt+1+1) := Fin.lastCases (Fin.last (bt+1))
    (fun i=>Fin.castAdd 1 (Fin.castAdd 1 i))
  have he : (appendOne (appendOne M N) P) ∘ ρ = appendOne M P := by
    funext l
    refine Fin.lastCases ?_ (fun i=>?_) l
    · simp [ρ,Function.comp_def,appendOne_aux]
    · simp only [Function.comp_apply,ρ,Fin.lastCases_castSucc]
      change appendOne (appendOne M N) P (Fin.castAdd 1 (Fin.castAdd 1 i)) =
        appendOne M P (Fin.castAdd 1 i)
      simp only [appendOne_old]
  simpa only [he] using binaryRelabelReduction basis ρ (appendOne (appendOne M N) P) U w

/-- Inverse weights are jointly available under exactly the source row
hypotheses, while every original matrix and unary remains in the language. -/
def inverseDiagonalFromRows (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (old : Fin bt) (hs : ∀ i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw : ∀ i,0<(w i : ℝ)) (hnonzero : ∀ i,realMatrix (M old) i≠0)
    (hproj : ∀ i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹))) U w)
      (evaluationProblem basis M U w) := by
  let G := gramCoreField (M old) w (max 1 (q-1))
  have hG : (realMatrix G).PosDef := by
    rw [show realMatrix G=gramCore (realMatrix (M old)) (realWeights w) from gramCoreField_real _ _]
    exact gramCore_posDef _ hs _ hw hnonzero hproj
  let hgram := gramAppendReduction basis M U w old (max 1 (q-1))
  have haux : (realMatrix (appendOne M G (Fin.last bt))).PosDef := by
    simpa only [appendOne_aux] using hG
  let hinv := inverseDiagonalAppendReduction basis (appendOne M G) U w (Fin.last bt) haux hw
  exact (skipMiddleReduction basis M G (Matrix.diagonal (fun i=>(w i)⁻¹)) U w).trans
    (hinv.trans hgram)

/-- The finite-language implication of source3.7, before composition with its
supplied original availability. All vertices, including isolates, get a loop. -/
def removePositiveWeights (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (old : Fin bt) (hs : ∀ i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw : ∀ i,0<(w i : ℝ)) (hnonzero : ∀ i,realMatrix (M old) i≠0)
    (hproj : ∀ i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M U (fun _=>1))
      (evaluationProblem basis M U w) := by
  let D := Matrix.diagonal (fun i=>(w i)⁻¹)
  have he : (appendOne M D) ∘ Fin.castAdd 1 = M := by
    funext l
    exact appendOne_old M D l
  have first : PromisePolyTimeTuringReduction (evaluationProblem basis M U (fun _=>1))
      (evaluationProblem basis (appendOne M D) U (fun _=>1)) := by
    simpa only [he] using binaryRelabelReduction basis (Fin.castAdd 1) (appendOne M D) U (fun _=>1)
  have hcancel : ∀ i,w i*appendOne M D (Fin.last bt) i i=1 := by
    intro i
    simp only [appendOne_aux,D,Matrix.diagonal_apply_eq]
    apply mul_inv_cancel₀
    intro h
    have hr := congrArg (fun x : K₀ => (x : ℝ)) h
    exact (ne_of_gt (hw i)) hr
  exact first.trans ((loopCancellationReduction basis (appendOne M D) U w (Fin.last bt) hcancel).trans
    (inverseDiagonalFromRows basis M U w old hs hw hnonzero hproj))

end PlanarHom.PositiveWeightRemoval
