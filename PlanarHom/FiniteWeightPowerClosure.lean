import PlanarHom.FiniteWeightPowerData
import PlanarHom.AuxiliaryFamilyElimination
import PlanarHom.PositiveWeightRemovalReduction
import PlanarHom.UnaryLoopRealization

/-! Any fixed finite collection of rational weight diagonals and their unaries
coexists with the complete original language over one finite real overfield.
The final oracle and its basis are exactly the original weighted source. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveWeightRemoval
open Complexity Complexity.MixedCode FiniteLanguageAliases SpectralFieldPresentation
open AlgebraicProductInterpolation ProductCompatibility
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q bt ut n dimension : ℕ}

def finitePowerAlphabet (w : Fin q→K₀) (rs : Fin n→ℚ) :=
  finiteAlphabet (finitePowerDiagonals w rs) (finitePowerUnaries w rs)

def finitePowerBasis (w : Fin q→K₀) (hw : ∀i,0<(w i : ℝ)) (rs : Fin n→ℚ) :=
  extensionBasis K₀ (finitePowerAlphabet w rs)
    (finiteAlphabet_algebraic _ _ (finitePowerDiagonals_algebraic w hw rs)
      (finitePowerUnaries_algebraic w hw rs))

def finitePowerMatrices (M : Fin bt→Matrix (Fin q) (Fin q) K₀)
    (w : Fin q→K₀) (rs : Fin n→ℚ) :
    Fin (bt+n)→Matrix (Fin q) (Fin q) (extensionField K₀ (finitePowerAlphabet w rs)) :=
  appendFamily (fun l i j=>sourceInclusion K₀ (finitePowerAlphabet w rs) (M l i j))
    (finiteBinaryValues K₀ (finitePowerDiagonals w rs) (finitePowerUnaries w rs))

def finitePowerUnaryLanguage (U : Fin ut→Fin q→K₀) (w : Fin q→K₀) (rs : Fin n→ℚ) :
    Fin (ut+n)→Fin q→extensionField K₀ (finitePowerAlphabet w rs) :=
  appendFamily (fun l i=>sourceInclusion K₀ (finitePowerAlphabet w rs) (U l i))
    (finiteUnaryValues K₀ (finitePowerDiagonals w rs) (finitePowerUnaries w rs))

theorem finitePower_inverse_zero (w : Fin q→K₀) (hw : ∀i,0<(w i : ℝ))
    (rs : Fin n→ℚ) (l : Fin n) (i j : Fin q)
    (h : (Matrix.diagonal (fun i=>(w i)⁻¹) i j : ℝ)=0) :
    finitePowerDiagonals w rs l i j=0 := by
  rw [inverseDiagonal_coe] at h
  exact diagonalPower_zero _ hw (rs l) i j h

omit [FiniteDimensional ℚ K₀] in
theorem finitePower_inverseUnary_zero (w : Fin q→K₀) (hw : ∀i,0<(w i : ℝ))
    (rs : Fin n→ℚ) (l : Fin n) (i : Fin q) (h : ((w i)⁻¹ : K₀).val=0) :
    finitePowerUnaries w rs l i=0 := by
  have hi : (w i : ℝ)⁻¹≠0 := inv_ne_zero (ne_of_gt (hw i))
  exact (hi h).elim

/-- Literal finite source3.7 closure with no temporary inverse labels in its
target and no restriction on how many times any fixed label occurs. -/
def finiteRationalDiagonalUnaryReduction (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt→Matrix (Fin q) (Fin q) K₀) (U : Fin ut→Fin q→K₀) (w : Fin q→K₀)
    (old : Fin bt) (hs : ∀i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw : ∀i,0<(w i : ℝ)) (hnonzero : ∀i,realMatrix (M old) i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j)
    (rs : Fin n→ℚ) :
    PromisePolyTimeTuringReduction
      (evaluationProblem (finitePowerBasis w hw rs) (finitePowerMatrices M w rs)
        (finitePowerUnaryLanguage U w rs)
        (fun i=>sourceInclusion K₀ (finitePowerAlphabet w rs) (w i)))
      (evaluationProblem basis M U w) := by
  let D := Matrix.diagonal (fun i=>(w i)⁻¹)
  let v := fun i=>(w i)⁻¹
  have inverse : PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M D) (appendOne U v) w)
      (evaluationProblem basis M U w) := by
    have hu := diagonalUnaryAppendReduction basis (appendOne M D) U w (Fin.last bt)
    simp only [appendOne_aux, D, Matrix.diagonal_apply_eq] at hu
    exact hu.trans (inverseDiagonalFromRows basis M U w old hs hw hnonzero hproj)
  have hzM : ∀l i j,(appendOne M D (Fin.last bt) i j : ℝ)=0→
      finitePowerDiagonals w rs l i j=0 := by
    simpa only [appendOne_aux] using finitePower_inverse_zero w hw rs
  have hpM : ∀l,HasProductMaps
      (fun p : Fin q×Fin q=>(appendOne M D (Fin.last bt) p.1 p.2 : ℝ))
      (fun p=>finitePowerDiagonals w rs l p.1 p.2) := by
    intro l
    simpa only [appendOne_aux] using inverseDiagonal_productMaps w hw (rs l)
  have hzU : ∀l i,(appendOne U v (Fin.last ut) i : ℝ)=0→finitePowerUnaries w rs l i=0 := by
    simpa only [appendOne_aux] using finitePower_inverseUnary_zero w hw rs
  have hpU : ∀l,HasProductMaps (fun i=>(appendOne U v (Fin.last ut) i : ℝ))
      (finitePowerUnaries w rs l) := by
    intro l
    simpa only [appendOne_aux] using inverseUnary_productMaps w hw (rs l)
  have joint := mixedFiniteOverfield_joint basis (appendOne M D) (appendOne U v) w
    (finitePowerDiagonals w rs) (finitePowerUnaries w rs)
    (finitePowerDiagonals_algebraic w hw rs) (finitePowerUnaries_algebraic w hw rs)
    (fun _=>Fin.last bt) (fun _=>Fin.last ut) hzM hpM hzU hpU
    (evaluationProblem basis M U w) inverse
  let φ := sourceInclusion K₀ (finitePowerAlphabet w rs)
  have hm : (fun l i j=>φ (appendOne M D l i j))=
      appendOne (fun l i j=>φ (M l i j)) (fun i j=>φ (D i j)) :=
    by simpa only [Function.comp_apply] using
      (appendOne_map (fun A : Matrix (Fin q) (Fin q) K₀=>fun i j=>φ (A i j)) M D)
  have hu : (fun l i=>φ (appendOne U v l i))=
      appendOne (fun l i=>φ (U l i)) (fun i=>φ (v i)) :=
    by simpa only [Function.comp_apply] using
      (appendOne_map (fun a : Fin q→K₀=>fun i=>φ (a i)) U v)
  dsimp only at joint
  change PromisePolyTimeTuringReduction
    (evaluationProblem (finitePowerBasis w hw rs)
      (appendFamily (fun l i j=>φ (appendOne M D l i j))
        (finiteBinaryValues K₀ (finitePowerDiagonals w rs) (finitePowerUnaries w rs)))
      (appendFamily (fun l i=>φ (appendOne U v l i))
        (finiteUnaryValues K₀ (finitePowerDiagonals w rs) (finitePowerUnaries w rs)))
      (fun i=>φ (w i))) _ at joint
  rw [hm,hu] at joint
  exact (skipAuxFamiliesReduction (finitePowerBasis w hw rs)
    (fun l i j=>φ (M l i j)) (fun i j=>φ (D i j))
    (finiteBinaryValues K₀ (finitePowerDiagonals w rs) (finitePowerUnaries w rs))
    (fun l i=>φ (U l i)) (fun i=>φ (v i))
    (finiteUnaryValues K₀ (finitePowerDiagonals w rs) (finitePowerUnaries w rs))
    (fun i=>φ (w i))).trans joint

omit [FiniteDimensional ℚ K₀] in
@[simp] theorem finitePowerMatrix_old_real (M : Fin bt→Matrix (Fin q) (Fin q) K₀)
    (w : Fin q→K₀) (rs : Fin n→ℚ) (l : Fin bt) (i j : Fin q) :
    (finitePowerMatrices M w rs (Fin.castAdd n l) i j : ℝ)=(M l i j : ℝ) := by
  simp only [finitePowerMatrices,appendFamily_old]
  rfl

omit [FiniteDimensional ℚ K₀] in
@[simp] theorem finitePowerMatrix_new_real (M : Fin bt→Matrix (Fin q) (Fin q) K₀)
    (w : Fin q→K₀) (rs : Fin n→ℚ) (l : Fin n) (i j : Fin q) :
    (finitePowerMatrices M w rs (Fin.natAdd bt l) i j : ℝ)=
      diagonalPower (fun i=>(w i : ℝ)) (rs l) i j := by
  simp only [finitePowerMatrices,appendFamily_new,finiteBinaryValues_coe,finitePowerDiagonals]

omit [FiniteDimensional ℚ K₀] in
@[simp] theorem finitePowerUnary_old_real (U : Fin ut→Fin q→K₀)
    (w : Fin q→K₀) (rs : Fin n→ℚ) (l : Fin ut) (i : Fin q) :
    (finitePowerUnaryLanguage U w rs (Fin.castAdd n l) i : ℝ)=(U l i : ℝ) := by
  simp only [finitePowerUnaryLanguage,appendFamily_old]
  rfl

omit [FiniteDimensional ℚ K₀] in
@[simp] theorem finitePowerUnary_new_real (U : Fin ut→Fin q→K₀)
    (w : Fin q→K₀) (rs : Fin n→ℚ) (l : Fin n) (i : Fin q) :
    (finitePowerUnaryLanguage U w rs (Fin.natAdd ut l) i : ℝ)=(w i : ℝ)^(rs l : ℝ) := by
  simp only [finitePowerUnaryLanguage,appendFamily_new,finiteUnaryValues_coe,finitePowerUnaries]

end PlanarHom.PositiveWeightRemoval
