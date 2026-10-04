import PlanarHom.BodyUnconditionalClassification
import PlanarHom.BiasedBooleanFoundationClosed
import PlanarHom.ActualTwinReduction

/-! NEW complete algebraic Proposition 2.2. The Boolean branch permits either
sign of its nonzero determinant, and the Potts clause covers every q >= 3. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode BooleanTensorEasyAssembly

theorem proposition22_boolean (L : RealLanguage 2 1 0) (hunit : ∀i,L.weights i=1)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i) (hp : ∀i j,0<L.matrices 0 i j)
    (hdet : L.matrices 0 0 0*L.matrices 0 1 1≠L.matrices 0 0 1^2) :
    (L.matrices 0 0 0=L.matrices 0 1 1 → L.problem.InFP) ∧
    (L.matrices 0 0 0≠L.matrices 0 1 1 → PromisedSharpPHard L.problem) := by
  let e : Fin 2≃Bool:=finTwoEquiv
  let B : Matrix Bool Bool L.field:=fun i j=>L.matricesK 0 (e.symm i) (e.symm j)
  have hm:L.matricesK=(fun _ : Fin 1=>L.matricesK 0):=funext (fun l=>congrArg L.matricesK (Subsingleton.elim l 0))
  have hu:L.unariesK=(fun u : Fin 0=>u.elim0):=funext (fun u=>u.elim0)
  have hw:L.weightsK=(fun _=>1):=funext (fun i=>Subtype.ext (hunit i))
  have heq : L.problem=evaluationProblem L.basis (fun _ : Fin 1=>L.matricesK 0) (fun u : Fin 0=>u.elim0) (fun _=>1):=by
    change evaluationProblem L.basis L.matricesK L.unariesK L.weightsK=_
    rw [hm,hu,hw]
  have hb : ∀i j,B i j=B j i:=fun i j=>Subtype.ext (hs _ _)
  have hpos : ∀i j,0<(B i j:ℝ):=fun i j=>hp _ _
  refine ⟨?_,?_⟩
  · intro hd
    have hbd : B false false=B true true:=Subtype.ext hd
    have hf:=equal_factor_inFP positiveIsingFoundation L.basis B (hb _ _) hbd (hpos _ _) (hpos _ _)
    have red:=ActualTwins.reindexReduction L.basis B (fun _=>1) e
    have hrec : (fun i j=>B (e i) (e j))=L.matricesK 0:=by ext i j; simp [B]
    rw [heq]
    rw [hrec] at red
    exact red.inFP hf
  · intro hne
    have hbn : B false false≠B true true:=fun h=>hne (congrArg L.field.val h)
    have hbd : B false false*B true true≠B false true^2:=fun h=>hdet (congrArg L.field.val h)
    have hh:=BiasedPositiveHardness.biasedBooleanFoundation L.field _ L.basis B hb hpos hbn hbd
    have red:=ActualTwins.homogeneousIdentityReduction L.basis B (fun _=>1) (L.matricesK 0) (fun _=>1)
      (fun g hg=>(g.toMultiGraph hg).partition_reindexColors (L.matricesK 0) (fun _=>1) e.symm)
    rw [heq]
    exact hh.trans red

theorem proposition22_equal_inFP (L : RealLanguage 2 1 0) (hunit : ∀i,L.weights i=1)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i) (hp : ∀i j,0<L.matrices 0 i j)
    (hd : L.matrices 0 0 0=L.matrices 0 1 1) : L.problem.InFP := by
  let e : Fin 2≃Bool:=finTwoEquiv
  let B : Matrix Bool Bool L.field:=fun i j=>L.matricesK 0 (e.symm i) (e.symm j)
  have hf:=equal_factor_inFP positiveIsingFoundation L.basis B
    (Subtype.ext (hs _ _)) (Subtype.ext hd) (hp _ _) (hp _ _)
  have red:=ActualTwins.reindexReduction L.basis B (fun _=>1) e
  have hrec : (fun i j=>B (e i) (e j))=L.matricesK 0:=by ext i j; simp [B]
  rw [hrec] at red
  have hm:L.matricesK=(fun _ : Fin 1=>L.matricesK 0):=funext (fun l=>congrArg L.matricesK (Subsingleton.elim l 0))
  have hu:L.unariesK=(fun u : Fin 0=>u.elim0):=funext (fun u=>u.elim0)
  have hw:L.weightsK=(fun _=>1):=funext (fun i=>Subtype.ext (hunit i))
  change (evaluationProblem L.basis L.matricesK L.unariesK L.weightsK).InFP
  rw [hm,hu,hw]
  exact red.inFP hf

theorem proposition22_boolean_isUnit (L : RealLanguage 2 1 0) (hunit : ∀i,L.weights i=1)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i) (hp : ∀i j,0<L.matrices 0 i j)
    (hInv : IsUnit (L.matrices 0)) :
    (L.matrices 0 0 0=L.matrices 0 1 1 → L.problem.InFP) ∧
    (L.matrices 0 0 0≠L.matrices 0 1 1 → PromisedSharpPHard L.problem) := by
  apply L.proposition22_boolean hunit hs hp
  have hd:=((Matrix.isUnit_iff_isUnit_det (L.matrices 0)).mp hInv).ne_zero
  intro h
  apply hd
  rw [Matrix.det_fin_two,hs 1 0,←pow_two,h,sub_self]

theorem proposition22_i (L : RealLanguage 2 1 0) (hunit : ∀i,L.weights i=1)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i) (hp : ∀i j,0<L.matrices 0 i j) :
    (L.matrices 0 0 0=L.matrices 0 1 1 → L.problem.InFP) ∧
    (IsUnit (L.matrices 0) → L.matrices 0 0 0≠L.matrices 0 1 1 → PromisedSharpPHard L.problem) :=
  ⟨L.proposition22_equal_inFP hunit hs hp,fun hi=>(L.proposition22_boolean_isUnit hunit hs hp hi).2⟩

theorem proposition22_potts (q : ℕ) (hq : 3≤q) : PromisedSharpPHard (pottsRationalProblem q) :=
  positivePottsFoundation q hq

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
