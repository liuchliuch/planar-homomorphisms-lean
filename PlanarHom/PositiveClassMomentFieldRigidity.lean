import PlanarHom.PositiveClassMomentSourceRigidity
import PlanarHom.ActualTwinReduction

/-! Fixed-field, arbitrary finite-color interface for actual numerical twin
quotients. Canonical algebraic presentations and color reindexing are bridged
by proved machines, never identified by equality of raw encodings. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveClassMomentRigidity
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode
variable {I : Type} [Fintype I] [Nonempty I]
variable {K : IntermediateField ℚ ℝ} {d : ℕ}

/-- Directly consumes the field-level weighted quotient problem produced by
the normalized moment construction, in its exact original output basis. -/
theorem field_weights_constant_of_not_hard (hPotts : PositivePottsFoundation)
    (basis : Module.Basis (Fin d) ℚ K) (C : Matrix I I K) (μ : I→K)
    (hs : ∀ i j,C i j=C j i) (hp : ∀ i j,0<(C i j:ℝ)) (hd : ∀ i,C i i=1)
    (hi : Function.Injective C) (hμ : ∀ i,0<(μ i:ℝ))
    (hnot : ¬PromisedSharpPHard (evaluationProblem basis (fun _:Fin 1=>C)
      (fun l:Fin 0=>l.elim0) μ)) : ∀ i j,μ i=μ j := by
  letI : FiniteDimensional ℚ K := FiniteDimensional.of_fintype_basis basis
  let e := (Fintype.equivFin I).symm
  letI : Nonempty (Fin (Fintype.card I)) := ⟨e.symm (Classical.choice inferInstance)⟩
  let L : RealLanguage (Fintype.card I) 1 0 := {
    matrices := fun _ i j=>(C (e i) (e j):ℝ)
    unaries := fun l=>l.elim0
    weights := fun i=>(μ (e i):ℝ)
    matrices_algebraic := fun _ i j=>(IsAlgebraic.of_finite ℚ (C (e i) (e j))).algHom K.val
    unaries_algebraic := fun l=>l.elim0
    weights_algebraic := fun i=>(IsAlgebraic.of_finite ℚ (μ (e i))).algHom K.val }
  have present := L.presentationDescentReduction K basis
    (fun _:Fin 1=>fun i j=>C (e i) (e j)) (fun l:Fin 0=>l.elim0) (fun i=>μ (e i))
    (fun _ _ _=>rfl) (fun l=>l.elim0) (fun _=>rfl)
  have red := present.trans (ActualTwins.reindexReduction basis C μ e)
  have hls : ∀ i j,L.matrices 0 i j=L.matrices 0 j i := by
    intro i j
    exact congrArg (fun x:K=>(x:ℝ)) (hs (e i) (e j))
  have hld : ∀ i,L.matrices 0 i i=1 := by
    intro i
    change (C (e i) (e i):ℝ)=1
    rw [hd]
    rfl
  have hli : Function.Injective (L.matrices 0) := by
    intro i j hij
    apply e.injective
    apply hi
    funext k
    apply Subtype.ext
    have he := congrFun hij (e.symm k)
    simpa only [L,e.apply_symm_apply] using he
  have he := weights_constant_of_not_hard hPotts L 0 hls (fun i j=>hp (e i) (e j))
    hld hli (fun i=>hμ (e i)) (fun hh=>hnot (hh.trans red))
  intro i j
  apply Subtype.ext
  simpa only [L,e.apply_symm_apply] using he (e.symm i) (e.symm j)

/-- Original-oracle form: each actual quotient moment can share the same
source oracle while retaining its supplied field presentation. -/
theorem field_weights_constant_of_available (hPotts : PositivePottsFoundation)
    (basis : Module.Basis (Fin d) ℚ K) (C : Matrix I I K) (μ : I→K)
    (hs : ∀ i j,C i j=C j i) (hp : ∀ i j,0<(C i j:ℝ)) (hd : ∀ i,C i i=1)
    (hi : Function.Injective C) (hμ : ∀ i,0<(μ i:ℝ))
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (evaluationProblem basis (fun _:Fin 1=>C)
      (fun l:Fin 0=>l.elim0) μ) base)
    (hnot : ¬PromisedSharpPHard base) : ∀ i j,μ i=μ j :=
  field_weights_constant_of_not_hard hPotts basis C μ hs hp hd hi hμ
    (fun hh=>hnot (hh.trans available))

end PlanarHom.PositiveClassMomentRigidity
