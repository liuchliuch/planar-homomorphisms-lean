import PlanarHom.FiniteWeightPowerClosure
import PlanarHom.DomainPositiveWeightRemoval
import PlanarHom.DomainUnaryLoopReduction

/-! Finite rational weight powers with unchanged intrinsic vertex domains,
retained companion policies and the original source field and oracle. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveWeightRemoval
open Complexity Complexity.MixedCode FiniteLanguageAliases SpectralFieldPresentation
open AlgebraicProductInterpolation ProductCompatibility PrescribedDomains
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q bt ut n dt dimension : ℕ}

/-- Every fixed finite family of rational diagonals and their unaries is jointly
available with prescribed domains. The ambient source label already admits
all domain pairs, and the original language contains an unrestricted domain. -/
def domainFiniteRationalDiagonalUnaryReduction (basis : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt→Matrix (Fin q) (Fin q) K₀) (U : Fin ut→Fin q→K₀) (w : Fin q→K₀)
    (Domains : Fin dt→Set (Fin q)) (policy : Fin bt→Fin dt→Fin dt→Prop)
    (typing : Fin ut→Fin dt→Prop) (old : Fin bt) (full : Fin dt)
    (hfull : Domains full=Set.univ) (hglobal : ∀x y,policy old x y)
    (hs : ∀i j,realMatrix (M old) i j=realMatrix (M old) j i)
    (hw : ∀i,0<(w i : ℝ)) (hnonzero : ∀i,realMatrix (M old) i≠0)
    (hproj : ∀i j,i≠j→∀t:ℝ,realMatrix (M old) i≠t • realMatrix (M old) j)
    (rs : Fin n→ℚ) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem (finitePowerBasis w hw rs) (finitePowerMatrices M w rs)
        (finitePowerUnaryLanguage U w rs)
        (fun i=>sourceInclusion K₀ (finitePowerAlphabet w rs) (w i)) Domains
        (appendFamily policy (fun _ : Fin n=>policy old))
        (appendFamily typing (fun (_ : Fin n) _=>True)))
      (domainEvaluationProblem basis M U w Domains policy typing) := by
  let D := Matrix.diagonal (fun i=>(w i)⁻¹)
  let v := fun i=>(w i)⁻¹
  have inverse : PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M D) (appendOne U v) w Domains
        (appendOne policy (policy old)) (appendOne typing (fun _=>True)))
      (domainEvaluationProblem basis M U w Domains policy typing) := by
    have hu := domainDiagonalUnaryAppendReduction basis (appendOne M D) U w Domains
      (appendOne policy (policy old)) typing (Fin.last bt) (fun _=>True)
      (by intro x _; simpa only [appendOne_aux] using hglobal x x)
    simp only [appendOne_aux,D,Matrix.diagonal_apply_eq] at hu
    exact hu.trans (domainInverseDiagonalFromRows basis M U w Domains policy typing
      old full hfull hglobal hs hw hnonzero hproj)
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
  have joint := domainMixedFiniteOverfield_joint basis (appendOne M D) (appendOne U v) w
    Domains (appendOne policy (policy old)) (appendOne typing (fun _=>True))
    (finitePowerDiagonals w rs) (finitePowerUnaries w rs)
    (fun _ : Fin n=>policy old) (fun (_ : Fin n) _=>True)
    (finitePowerDiagonals_algebraic w hw rs) (finitePowerUnaries_algebraic w hw rs)
    (fun _=>Fin.last bt) (fun _=>Fin.last ut)
    (by intro _ x y h; simpa only [appendOne_aux] using h)
    (by intro _ x _; simp only [appendOne_aux])
    hzM hpM hzU hpU (domainEvaluationProblem basis M U w Domains policy typing) inverse
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
    (domainEvaluationProblem (finitePowerBasis w hw rs)
      (appendFamily (fun l i j=>φ (appendOne M D l i j))
        (finiteBinaryValues K₀ (finitePowerDiagonals w rs) (finitePowerUnaries w rs)))
      (appendFamily (fun l i=>φ (appendOne U v l i))
        (finiteUnaryValues K₀ (finitePowerDiagonals w rs) (finitePowerUnaries w rs)))
      (fun i=>φ (w i)) Domains
      (appendFamily (appendOne policy (policy old)) (fun _ : Fin n=>policy old))
      (appendFamily (appendOne typing (fun _=>True)) (fun (_ : Fin n) _=>True))) _ at joint
  rw [hm,hu] at joint
  exact (domainSkipAuxFamiliesReduction (finitePowerBasis w hw rs)
    (fun l i j=>φ (M l i j)) (fun i j=>φ (D i j))
    (finiteBinaryValues K₀ (finitePowerDiagonals w rs) (finitePowerUnaries w rs))
    (fun l i=>φ (U l i)) (fun i=>φ (v i))
    (finiteUnaryValues K₀ (finitePowerDiagonals w rs) (finitePowerUnaries w rs))
    (fun i=>φ (w i)) Domains policy (policy old) (fun _ : Fin n=>policy old)
    typing (fun _=>True) (fun (_ : Fin n) _=>True)).trans joint

end PlanarHom.PositiveWeightRemoval
